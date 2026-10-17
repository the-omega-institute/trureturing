/- Transient comparison on one actual original fuel-2 bound leaf.
No complete global acceptance or retained bind-only application is claimed. -/
import D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadoutsProbe
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadouts
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)
private def triangles : Fin 16 → TriangleReadout := ![⟨(4991, (0, 0)), ![some 0,some 0,some 0,some 1,some 1,some 2,some 1,some 2,none,some 1], (-5597207602580685)⟩,
  ⟨(262, (6, 0)), ![some 0,some 0,some 0,some 1,some 1,some 2,some 1,some 1,some 1,some 1], (-5876335451118405)⟩,
  ⟨(8955, (6, 6)), ![some 0,some 1,some 1,some 1,some 2,none,some 2,some 2,some 2,some 0], (3853149116068980)⟩,
  ⟨(2673, (6, 6)), ![some 0,some 1,some 1,some 1,some 1,some 1,some 2,some 2,some 2,some 0], (9863175761961795)⟩,
  ⟨(10154, (5, 14)), ![some 2,some 1,some 0,some 1,some 1,some 2,some 0,some 2,none,some 1], (1310221483279800)⟩,
  ⟨(3161, (9, 12)), ![some 2,some 1,some 0,some 1,some 1,some 2,some 0,some 1,some 1,some 1], (1499402310054285)⟩,
  ⟨(5007, (9, 12)), ![some 1,some 1,some 1,some 0,some 2,none,some 0,some 2,some 2,some 0], (-6419922013639680)⟩,
  ⟨(82, (9, 6)), ![some 1,some 1,some 1,some 0,some 2,some 2,some 0,some 1,some 1,some 0], (-6533542716730575)⟩,
  ⟨(10162, (5, 14)), ![some 2,some 1,some 0,some 1,some 1,some 2,some 0,some 1,none,some 1], (1499402310054285)⟩,
  ⟨(921, (4, 8)), ![some 2,some 2,some 0,some 1,some 1,some 2,some 0,some 1,some 1,some 1], (5257607032772640)⟩,
  ⟨(4930, (2, 6)), ![some 1,some 1,some 1,some 0,some 1,none,some 0,some 2,some 2,some 0], (-6533542716730575)⟩,
  ⟨(2226, (3, 12)), ![some 1,some 2,some 1,some 0,some 2,some 2,some 0,some 1,some 1,some 0], (7298224963841175)⟩,
  ⟨(3559, (9, 12)), ![some 2,some 1,some 0,some 1,some 1,some 1,some 0,some 1,some 2,some 1], (2658436026382500)⟩,
  ⟨(14983, (0, 8)), ![some 2,none,some 0,some 1,some 1,some 1,some 0,some 1,some 1,some 1], (1910405242148130)⟩,
  ⟨(1708, (3, 12)), ![some 1,some 2,some 1,some 0,some 1,some 2,some 0,some 2,some 2,some 0], (4075924531120260)⟩,
  ⟨(13701, (3, 14)), ![some 2,none,some 1,some 0,some 2,some 2,some 0,some 1,some 1,some 0], (1593154150886025)⟩]
private def singletons : Fin 13 → SingletonReadout := ![⟨(2875, (0, 0)), ![some 0,some 1,some 1,some 1,some 2,some 1,none,some 1,some 1], (-880826071055385)⟩,
  ⟨(986, (4, 2)), ![some 0,some 2,some 1,some 2,some 1,some 2,some 2,some 0,some 1], (113559891444090)⟩,
  ⟨(1242, (0, 12)), ![some 1,some 1,some 1,some 1,some 2,some 1,none,some 0,some 0], (-870008822931885)⟩,
  ⟨(2528, (8, 14)), ![some 2,some 0,some 0,some 1,some 2,some 1,none,some 1,some 1], (-2265590076897420)⟩,
  ⟨(368, (8, 12)), ![some 1,some 0,some 1,some 2,some 1,some 2,some 2,some 0,some 1], (-70945439936280)⟩,
  ⟨(1830, (3, 12)), ![some 1,some 0,some 0,some 1,some 2,some 1,none,some 0,some 0], (-1116663894919755)⟩,
  ⟨(3007, (3, 14)), ![some 2,some 0,some 0,some 1,some 1,some 1,none,some 1,some 1], (-1413962239765530)⟩,
  ⟨(1355, (3, 6)), ![some 1,some 0,some 0,some 1,some 1,some 1,none,some 0,some 0], (-419263547625195)⟩,
  ⟨(103, (5, 14)), ![some 2,some 0,some 1,some 2,some 1,some 2,some 2,some 0,some 1], (1994869447264785)⟩,
  ⟨(556, (11, 14)), ![some 2,some 0,some 0,some 1,some 1,some 1,some 2,some 1,some 1], (-1379582934588495)⟩,
  ⟨(231, (9, 12)), ![some 1,some 0,some 1,some 2,some 1,some 2,some 1,some 0,some 1], (1281407355645690)⟩,
  ⟨(561, (11, 14)), ![some 2,some 0,some 0,some 1,some 1,some 1,some 2,some 0,some 0], (-1667028171566940)⟩,
  ⟨(3493, (9, 12)), ![none,some 0,some 1,some 2,some 1,some 2,some 1,some 0,some 1], (-1161716989192305)⟩]
private def triangleSelection : Fin 16 → Fin 16 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
private def singletonSelection : Fin 16 → Fin 13 := ![0,1,1,2,3,4,5,4,6,4,7,8,9,10,11,12]
private def actualPartial : Partial (Fin 20) (Fin 4) := ![some 0,some 0,some 0,some 0,some 0,some 1,some 1,some 1,some 2,some 1,some 1,some 1,some 2,some 1,some 1,some 2,some 2,some 1,some 2,none]
private theorem triangle_accepted : ∀ j, checkTriangle (triangles j) = true := by
  decide +kernel
private theorem singleton_accepted : ∀ j, checkSingleton (singletons j) = true := by
  decide +kernel
private theorem leaf_accepted :
    checkBound triangles singletons triangleSelection singletonSelection actualPartial = true := by
  decide +kernel
example (e : Event (Fin 20) (Fin 4)) (compatible : Compatible actualPartial e) :
    scale ≤ score F1 F2 e :=
  checked_bound triangles singletons triangle_accepted singleton_accepted
    triangleSelection singletonSelection actualPartial leaf_accepted e compatible
#print axioms triangle_accepted
#print axioms singleton_accepted
#print axioms leaf_accepted
end D5.S3.Quantum.Entanglement.EJM.EJMSharedLocalReadoutsProbe
