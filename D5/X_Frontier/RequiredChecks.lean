/- GID: D5/X_Frontier/RequiredChecks
   generality: G
   mirror-B: none(waiver:hosting-configuration-ticket)
   mirror-E: none(waiver:hosting-configuration-ticket)
   anchors: [golden-ledger-spec-v7.11-human-gates]
   digest: A human operator must configure and verify required checks on the hosting platform. -/

/-- TASK D5-T0007 | 难度:2 | 依赖:欠(human-hosting-access) | 尝试:0
    提示:Require the lint and build job names after verifying them in repository settings.
    尸检:none -/
def requiredChecksTicket : Unit := ()
