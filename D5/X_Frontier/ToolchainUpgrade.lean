/- GID: D5/X_Frontier/ToolchainUpgrade
   generality: G
   mirror-B: none(waiver:no-M0-upgrade)
   mirror-E: none(waiver:no-upgrade-diff-artifact)
   anchors: [spec/v7.11/SL-014]
   digest: Activate statement-preserving upgrade-diff enforcement at the first toolchain upgrade. -/

/-- TASK D5-T0010 | 难度:3 | 依赖:欠(first-toolchain-upgrade) | 尝试:0
    提示:At the first upgrade, compare declaration signatures against the protected base and permit proof-only edits.
    尸检:none -/
def toolchainUpgradeTicket : Unit := ()
