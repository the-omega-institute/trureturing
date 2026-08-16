/- GID: D5/X_Frontier/RequiredChecks
   generality: G
   mirror-B: none(waiver:hosting-configuration-ticket)
   mirror-E: none(waiver:hosting-configuration-ticket)
   anchors: []
   digest: A human operator must install the bootstrap and configure required checks on the hosting platform. -/

/- TASK D5-T0007
    Require the lint and build job names after verifying them in repository settings. -/

/- TASK D5-T0017
    An admin must make the one-time trusted injection of the harness and CI into dev, then configure required_status_checks and enforce_admins=true.
    曾试过并失败:A candidate-only pull_request_target workflow cannot run before that workflow exists on dev; candidate-as-baseline therefore was not a pre-merge machine gate. -/
