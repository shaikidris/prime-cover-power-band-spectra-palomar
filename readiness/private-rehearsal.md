# D31 private rehearsal

The user requires publication to be the final step before Palomar. The audit
branch workflow `.github/workflows/d31-private-readiness.yml` runs on pushes
that change it or `readiness/private_prepare.py`. The submitted source remains
main commit `454743470f6aff2e7f7f8ac79a7a2a7279e60ada`; orchestration changes
must never be substituted as the source under verification.

The workflow derives its build/execute steps from PalomarSubmission
`ef2fa1eadcb246c2346ddba39b52eaa53d4bb763` (MIT notice retained alongside this
file). It checks out that upstream code without modifications. An ephemeral
Actions contents-read token authenticates only the trusted preparation source
fetch, scoped to this repository. The wrapper fails on a non-prepared report,
wrong source/tool commit, or persisted credential configuration. Separate
execution steps reject any remaining private transport environment. No token
is written to a report, artifact or Git configuration, and no private content
is sent to the public verifier fork.

Accept P6a only from its actual prepared report, P6b only from a bound
mechanical `status: pass` report, and P6c only from a bound successful render
report plus visual inspection. A successful wrapper or workflow setup is not
sufficient. Public anonymous source availability remains the final P5 gate;
private authentication is disclosed and does not establish that property.
