"""D31-only private transport wrapper; the pinned Palomar verifier is unchanged.

The Actions read token is used by trusted preparation only, as an in-memory Git
HTTP header scoped to the exact source repository. It is never saved in a Git
configuration, report, artifact or later protected execution environment.
"""
import argparse
import base64
import hashlib
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import uuid


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["preflight", "full", "render"], required=True)
    parser.add_argument("--pipeline", type=Path, required=True)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    pipeline = args.pipeline.resolve()
    values = json.loads(args.inputs.read_text())
    expected_repo = "shaikidris/prime-cover-power-band-spectra-palomar"
    expected_commit = "454743470f6aff2e7f7f8ac79a7a2a7279e60ada"
    expected_verifier = "ef2fa1eadcb246c2346ddba39b52eaa53d4bb763"
    if values["repository"] != expected_repo or values["commit"] != expected_commit:
        raise ValueError("Inputs differ from the reviewed D31 source freeze")
    actual_verifier = subprocess.check_output(["git", "-C", str(pipeline), "rev-parse", "HEAD"], text=True).strip()
    if actual_verifier != expected_verifier:
        raise ValueError("Verifier checkout is not the reviewed immutable revision")
    subprocess.run(["git", "-C", str(pipeline), "diff", "--quiet", "HEAD"], check=True)
    token = os.environ.pop("D31_SOURCE_TOKEN", "")
    if not token:
        raise ValueError("Private preparation requires the Actions read token")
    environment = os.environ.copy()
    for name in list(environment):
        if name.startswith("GIT_CONFIG_") or name.startswith("GIT_TRACE") or name == "GIT_CURL_VERBOSE":
            environment.pop(name)
    header = base64.b64encode(("x-access-token:" + token).encode()).decode()
    environment.update({
        "GIT_CONFIG_COUNT": "1",
        "GIT_CONFIG_KEY_0": f"http.https://github.com/{expected_repo}.extraheader",
        "GIT_CONFIG_VALUE_0": "AUTHORIZATION: basic " + header,
        "GIT_TERMINAL_PROMPT": "0",
    })
    values["request_id"] = uuid.uuid4().hex if args.mode == "render" else uuid.uuid4().hex[:12]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.mode == "render":
        command = [sys.executable, "-m", "scripts.render_challenge", "prepare"]
        for field in ["repository", "commit", "challenge_sha256", "project_path", "challenge_path",
                      "solution_path", "comparator_config_path", "lakefile_path", "lean_toolchain_path"]:
            command += ["--" + field.replace("_", "-"), values.get(field, "")]
    else:
        values["mode"] = args.mode
        event = args.output.with_suffix(".event.json")
        event.write_text(json.dumps({"inputs": values}, indent=2) + "\n")
        command = [sys.executable, "-m", "scripts.verify_submission", "prepare", "--event", str(event.resolve()),
                   "--licensee", shutil.which("bundle") or "/missing-bundle"]
    command += ["--work-dir", str(args.work_dir.resolve()), "--output", str(args.output.resolve())]
    subprocess.run(command, cwd=pipeline, env=environment, check=True)
    environment.clear()
    token = header = ""
    report = json.loads(args.output.read_text())
    expected_status = "pending"
    if report.get("status") != expected_status or report.get("stage") != "prepared" or report.get("errors"):
        raise ValueError(f"Private {args.mode} preparation did not pass: {report.get('status')}")
    checkout = args.work_dir / "source"
    resolved = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    if resolved != expected_commit:
        raise ValueError("Prepared checkout does not match the frozen source")
    config_names = subprocess.run(["git", "-C", str(checkout), "config", "--local", "--name-only", "--get-regexp",
                                   "(extraheader|credential)"], text=True, capture_output=True)
    if config_names.returncode != 1:
        raise ValueError("Prepared Git checkout has a credential-related configuration or could not be audited")
    receipt = {
        "scope": "private Linux rehearsal; anonymous source availability is deferred to the final publication gate",
        "mode": args.mode, "source_commit": expected_commit, "verifier_commit": actual_verifier,
        "request_id": values["request_id"], "inputs": values,
        "source_transport": "ephemeral repository-scoped Actions read token during trusted preparation only",
        "git_credentials_persisted": False, "verifier_source_modified": False,
        "verifier_sha256": hashlib.sha256((pipeline / "scripts/verify_submission.py").read_bytes()).hexdigest(),
        "renderer_sha256": hashlib.sha256((pipeline / "scripts/render_challenge.py").read_bytes()).hexdigest(),
    }
    args.output.with_suffix(".transport.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Private {args.mode} preparation passed for {expected_commit}; no credential was persisted.")


if __name__ == "__main__":
    main()
