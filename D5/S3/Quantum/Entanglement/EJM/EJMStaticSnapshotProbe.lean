/- Transient exact application, not retained library content or global acceptance.
The actual original bound leaf has fuel 2, index 0, and one unknown coordinate.
All 32 row/action literals and the original partial come from the existing
2497-context trace. Native source selection is untrusted; the kernel must
check the complete direct snapshot before this exact application is accepted. -/

import D5.S3.Quantum.Entanglement.EJM.EJMStaticGlobalReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMStaticSnapshotProbe
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMStaticGlobalReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)

private def actualPartial : Partial (Fin 20) (Fin 4) := ![some 0,some 0,some 0,some 0,some 0,some 1,some 1,some 1,some 2,some 1,some 1,some 1,some 2,some 1,some 1,some 2,some 2,some 1,some 2,none]

private def actualSnapshot : Cache :=
  ⟨![⟨(4991, (0, 0)), ⟨3694500, (-5597207602580685), 0x1000000000, 0x93000048c00023f0a00d4⟩⟩,
    ⟨(262, (6, 0)), ⟨2832000, (-5876335451118405), 0x0, 0x0⟩⟩,
    ⟨(8955, (6, 6)), ⟨3679630, (3853149116068980), 0x1000000000, 0x5488002a3430150a180a79⟩⟩,
    ⟨(2673, (6, 6)), ⟨1960880, (9863175761961795), 0x0, 0x0⟩⟩,
    ⟨(10154, (5, 14)), ⟨2800680, (1310221483279800), 0x1110000000, 0x6e600036a0001b18000d6d⟩⟩,
    ⟨(3161, (9, 12)), ⟨84430, (1499402310054285), 0x0, 0x0⟩⟩,
    ⟨(5007, (9, 12)), ⟨5022625, (-6419922013639680), 0x1100000000, 0x97428048c000232c000c5⟩⟩,
    ⟨(82, (9, 6)), ⟨2534375, (-6533542716730575), 0x0, 0x0⟩⟩,
    ⟨(10162, (5, 14)), ⟨2878805, (1499402310054285), 0x1110000000, 0x6ea00036c18c18b2000d75⟩⟩,
    ⟨(921, (4, 8)), ⟨4804400, (5257607032772640), 0x0, 0x0⟩⟩,
    ⟨(4930, (2, 6)), ⟨2856875, (-6533542716730575), 0x1111000000, 0x807a8680314000132180052⟩⟩,
    ⟨(2226, (3, 12)), ⟨4694505, (7298224963841175), 0x0, 0x0⟩⟩,
    ⟨(3559, (9, 12)), ⟨6930, (2658436026382500), 0x0, 0x0⟩⟩,
    ⟨(14983, (0, 8)), ⟨4867170, (1910405242148130), 0x1111111100, 0x4c88f438031252c0f8090047d⟩⟩,
    ⟨(1708, (3, 12)), ⟨4788130, (4075924531120260), 0x0, 0x0⟩⟩,
    ⟨(13701, (3, 14)), ⟨4787545, (1593154150886025), 0x1111111100, 0x186a200830792c0b4800020b⟩⟩],
   ![⟨(2875, (0, 0)), ⟨535780, (-880826071055385), 0x110000000, 0x1f60000f74300772f0021c⟩⟩,
    ⟨(986, (4, 2)), ⟨817030, (113559891444090), 0x0, 0x0⟩⟩,
    ⟨(986, (4, 2)), ⟨817030, (113559891444090), 0x0, 0x0⟩⟩,
    ⟨(1242, (0, 12)), ⟨1000625, (-870008822931885), 0x110000000, 0x801906800b400004e18000c⟩⟩,
    ⟨(2528, (8, 14)), ⟨498400, (-2265590076897420), 0x111000000, 0xc81a70600c5030045818013e⟩⟩,
    ⟨(368, (8, 12)), ⟨801275, (-70945439936280), 0x0, 0x0⟩⟩,
    ⟨(1830, (3, 12)), ⟨977525, (-1116663894919755), 0x111100000, 0x80e08c805cc000286300078⟩⟩,
    ⟨(368, (8, 12)), ⟨801275, (-70945439936280), 0x0, 0x0⟩⟩,
    ⟨(3007, (3, 14)), ⟨508905, (-1413962239765530), 0x111100000, 0x821a8001000000790c0022c⟩⟩,
    ⟨(368, (8, 12)), ⟨801275, (-70945439936280), 0x0, 0x0⟩⟩,
    ⟨(1355, (3, 6)), ⟨490000, (-419263547625195), 0x111100000, 0x1803c00801e000007c000011⟩⟩,
    ⟨(103, (5, 14)), ⟨569375, (1994869447264785), 0x0, 0x0⟩⟩,
    ⟨(556, (11, 14)), ⟨507025, (-1379582934588495), 0x0, 0x0⟩⟩,
    ⟨(231, (9, 12)), ⟨813150, (1281407355645690), 0x0, 0x0⟩⟩,
    ⟨(561, (11, 14)), ⟨975775, (-1667028171566940), 0x0, 0x0⟩⟩,
    ⟨(3493, (9, 12)), ⟨813154, (-1161716989192305), 0x111111110, 0x482333e00c012c02640000e7⟩⟩]⟩

private theorem snapshot_accepted : checkBoundSnapshot actualSnapshot actualPartial = true := by
  decide +kernel

example (e : Event (Fin 20) (Fin 4)) (compatible : Compatible actualPartial e) :
    scale ≤ score F1 F2 e :=
  checked_bound_snapshot actualSnapshot actualPartial snapshot_accepted e compatible

#print axioms snapshot_accepted

end D5.S3.Quantum.Entanglement.EJM.EJMStaticSnapshotProbe
