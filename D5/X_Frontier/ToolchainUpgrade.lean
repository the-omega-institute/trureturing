/- GID: D5/X_Frontier/ToolchainUpgrade
   generality: G
   mirror-B: none(waiver:no-M0-upgrade)
   mirror-E: none(waiver:no-upgrade-diff-artifact)
   anchors: []
   digest: Activate statement-preserving upgrade-diff enforcement at the first toolchain upgrade. -/

/-- TASK D5-T0010
    At the first upgrade, compare declaration signatures against the protected base and permit proof-only edits. -/
def toolchainUpgradeTicket : Unit := ()
