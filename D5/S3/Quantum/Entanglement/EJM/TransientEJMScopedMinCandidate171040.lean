/- Prepared transient original-domain semantic bound; uncompiled.
Actual context: depth17, code1040, original node440, fuel4.
All 32 original factors and scale6987435 are preserved. Every proposed
row/action association and scaled lower is checked below by the kernel.
The three scope checks exhaust all four choices at each scoped variable.
The theorem bounds completions of this prefix; it does not prove the
original DAG's Accepted proposition or complete global coverage. -/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMScopedMinCandidate171040
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym triangleRows singletonRows)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (CachedLocal)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (TriangleValid SingletonValid triangle_valid_lower singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock score)
open scoped BigOperators

private def mkTriangle (s : Fin 41294 × LocalSym) : CachedLocal 41294 :=
  ⟨s, EJMTriangleCacheData.mirror s.1⟩
private def mkSingleton (s : Fin 8689 × LocalSym) : CachedLocal 8689 :=
  ⟨s, EJMSingletonCacheData.mirror s.1⟩

private theorem triangle_from_assignment (s : Fin 41294 × LocalSym)
    (p : Partial (Fin 10) (Fin 4))
    (checked : EJMTriangleCacheData.assignment s.1 = trianglePartialAct s.2 p) :
    TriangleValid (mkTriangle s) p := by
  refine ⟨rfl, ?_⟩
  change (triangleRows s.1).assignment = trianglePartialAct s.2 p
  rw [← EJMTriangleCacheReceipts.assignment_eq]
  exact checked

private theorem singleton_from_assignment (s : Fin 8689 × LocalSym)
    (p : Partial (Fin 9) (Fin 4))
    (checked : EJMSingletonCacheData.assignment s.1 = singletonPartialAct s.2 p) :
    SingletonValid (mkSingleton s) p := by
  refine ⟨rfl, ?_⟩
  change (singletonRows s.1).assignment = singletonPartialAct s.2 p
  rw [← EJMSingletonCacheReceipts.assignment_eq]
  exact checked

private theorem compatible_fill (p : Partial (Fin 20) (Fin 4))
    (e : Event (Fin 20) (Fin 4)) (hp : Compatible p e) (i : Fin 20) :
    Compatible (Function.update p i (some (e i))) e := by
  intro j a ha
  by_cases same : j = i
  · subst j
    simpa only [Function.update_self, Option.some.injEq] using ha
  · rw [Function.update_of_ne same] at ha
    exact hp j a ha

private theorem compatible_project {n : ℕ} (p : Partial (Fin 20) (Fin 4))
    (e : Event (Fin 20) (Fin 4)) (projection : Fin n → Fin 20)
    (hp : Compatible p e) : Compatible (p ∘ projection) (e ∘ projection) := by
  intro i a ha
  exact hp (projection i) a ha

private def group0Partial (a b : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (prefixPartial 17 1040) (17 : Fin 20) (some a)) (18 : Fin 20) (some b))

private theorem group0Compatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    Compatible (group0Partial (e 17) (e 18)) e := by
  unfold group0Partial
  exact (compatible_fill _ _ (compatible_fill _ _ hp 17) 18)

private def group1Partial (c : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (prefixPartial 17 1040) (19 : Fin 20) (some c))

private theorem group1Compatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    Compatible (group1Partial (e 19)) e := by
  unfold group1Partial
  exact (compatible_fill _ _ hp 19)

private def group2Partial (a : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (prefixPartial 17 1040) (17 : Fin 20) (some a))

private theorem group2Compatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    Compatible (group2Partial (e 17)) e := by
  unfold group2Partial
  exact (compatible_fill _ _ hp 17)

private def state00 : Fin 41294 × LocalSym :=
  (15346, (0, 0))
private def value00 : ℤ :=
  (-4039106876650755)

private theorem assignment00 : 
    EJMTriangleCacheData.assignment (state00).1 =
      trianglePartialAct (state00).2 ((prefixPartial 17 1040) ∘ lhsTriangle 0) := by
  decide +kernel

private theorem lower00 : 
    (mkTriangle (state00)).row.lower = value00 := by
  decide +kernel

private theorem bound00 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value00 ≤ triangleBlock F1 0 e := by
  have valid := triangle_from_assignment (state00) ((prefixPartial 17 1040) ∘ lhsTriangle 0)
    (assignment00)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsTriangle 0)
    hp
  have bound := triangle_valid_lower (mkTriangle (state00))
    ((prefixPartial 17 1040) ∘ lhsTriangle 0) (e ∘ lhsTriangle 0) valid compatible
  change (mkTriangle (state00)).row.lower ≤
    triangleBlock F1 0 e at bound
  rw [lower00] at bound
  exact bound

private def state01 (a b : Fin 4) : Fin 41294 × LocalSym :=
  ![![(2, (7, 0)), (5, (6, 0)), (8, (6, 0)), (8, (6, 1))], ![(26, (6, 0)), (29, (6, 0)), (32, (6, 0)), (32, (6, 1))], ![(36, (6, 2)), (43, (6, 2)), (39, (6, 2)), (47, (6, 2))], ![(36, (6, 3)), (43, (6, 3)), (47, (6, 3)), (39, (6, 3))]] a b
private def value01 (a b : Fin 4) : ℤ :=
  ![![(-3842827060476495), (-5890623365193840), (-4072016675335245), (-4072016675335245)], ![(-4039106876650755), (-4908738021733455), (-5580512894469240), (-5580512894469240)], ![(-4456228796410755), (-6261360113060325), (-5563169626615965), (-5776976536083480)], ![(-4456228796410755), (-6261360113060325), (-5776976536083480), (-5563169626615965)]] a b

private theorem assignment01 : ∀ (a b : Fin 4), 
    EJMTriangleCacheData.assignment (state01 a b).1 =
      trianglePartialAct (state01 a b).2 ((group0Partial a b) ∘ lhsTriangle 1) := by
  decide +kernel

private theorem lower01 : ∀ (a b : Fin 4), 
    (mkTriangle (state01 a b)).row.lower = value01 a b := by
  decide +kernel

private theorem bound01 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value01 (e 17) (e 18) ≤ triangleBlock F1 1 e := by
  have valid := triangle_from_assignment (state01 (e 17) (e 18)) ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 1)
    (assignment01 (e 17) (e 18))
  have compatible := compatible_project (group0Partial (e 17) (e 18)) e (lhsTriangle 1)
    (group0Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state01 (e 17) (e 18)))
    ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 1) (e ∘ lhsTriangle 1) valid compatible
  change (mkTriangle (state01 (e 17) (e 18))).row.lower ≤
    triangleBlock F1 1 e at bound
  rw [lower01 (e 17) (e 18)] at bound
  exact bound

private def state02 (c : Fin 4) : Fin 41294 × LocalSym :=
  ![(2, (9, 0)), (5, (8, 0)), (8, (8, 0)), (8, (8, 1))] c
private def value02 (c : Fin 4) : ℤ :=
  ![(-3842827060476495), (-5890623365193840), (-4072016675335245), (-4072016675335245)] c

private theorem assignment02 : ∀ (c : Fin 4), 
    EJMTriangleCacheData.assignment (state02 c).1 =
      trianglePartialAct (state02 c).2 ((group1Partial c) ∘ lhsTriangle 2) := by
  decide +kernel

private theorem lower02 : ∀ (c : Fin 4), 
    (mkTriangle (state02 c)).row.lower = value02 c := by
  decide +kernel

private theorem bound02 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value02 (e 19) ≤ triangleBlock F1 2 e := by
  have valid := triangle_from_assignment (state02 (e 19)) ((group1Partial (e 19)) ∘ lhsTriangle 2)
    (assignment02 (e 19))
  have compatible := compatible_project (group1Partial (e 19)) e (lhsTriangle 2)
    (group1Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state02 (e 19)))
    ((group1Partial (e 19)) ∘ lhsTriangle 2) (e ∘ lhsTriangle 2) valid compatible
  change (mkTriangle (state02 (e 19))).row.lower ≤
    triangleBlock F1 2 e at bound
  rw [lower02 (e 19)] at bound
  exact bound

private def state03 (a : Fin 4) : Fin 41294 × LocalSym :=
  ![(0, (6, 0)), (2, (6, 0)), (2, (6, 2)), (2, (6, 3))] a
private def value03 (a : Fin 4) : ℤ :=
  ![(-333398033381595), (-3842827060476495), (-3842827060476495), (-3842827060476495)] a

private theorem assignment03 : ∀ (a : Fin 4), 
    EJMTriangleCacheData.assignment (state03 a).1 =
      trianglePartialAct (state03 a).2 ((group2Partial a) ∘ lhsTriangle 3) := by
  decide +kernel

private theorem lower03 : ∀ (a : Fin 4), 
    (mkTriangle (state03 a)).row.lower = value03 a := by
  decide +kernel

private theorem bound03 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value03 (e 17) ≤ triangleBlock F1 3 e := by
  have valid := triangle_from_assignment (state03 (e 17)) ((group2Partial (e 17)) ∘ lhsTriangle 3)
    (assignment03 (e 17))
  have compatible := compatible_project (group2Partial (e 17)) e (lhsTriangle 3)
    (group2Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state03 (e 17)))
    ((group2Partial (e 17)) ∘ lhsTriangle 3) (e ∘ lhsTriangle 3) valid compatible
  change (mkTriangle (state03 (e 17))).row.lower ≤
    triangleBlock F1 3 e at bound
  rw [lower03 (e 17)] at bound
  exact bound

private def state04 : Fin 41294 × LocalSym :=
  (15219, (6, 0))
private def value04 : ℤ :=
  (-6261360113060325)

private theorem assignment04 : 
    EJMTriangleCacheData.assignment (state04).1 =
      trianglePartialAct (state04).2 ((prefixPartial 17 1040) ∘ lhsTriangle 4) := by
  decide +kernel

private theorem lower04 : 
    (mkTriangle (state04)).row.lower = value04 := by
  decide +kernel

private theorem bound04 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value04 ≤ triangleBlock F1 4 e := by
  have valid := triangle_from_assignment (state04) ((prefixPartial 17 1040) ∘ lhsTriangle 4)
    (assignment04)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsTriangle 4)
    hp
  have bound := triangle_valid_lower (mkTriangle (state04))
    ((prefixPartial 17 1040) ∘ lhsTriangle 4) (e ∘ lhsTriangle 4) valid compatible
  change (mkTriangle (state04)).row.lower ≤
    triangleBlock F1 4 e at bound
  rw [lower04] at bound
  exact bound

private def state05 (a b : Fin 4) : Fin 41294 × LocalSym :=
  ![![(1282, (1, 0)), (1530, (0, 0)), (1618, (0, 0)), (1618, (0, 1))], ![(1292, (1, 0)), (1533, (0, 0)), (1622, (0, 0)), (1622, (0, 1))], ![(1302, (1, 0)), (1536, (0, 0)), (1626, (0, 0)), (1630, (0, 1))], ![(1302, (1, 1)), (1536, (0, 1)), (1630, (0, 0)), (1626, (0, 1))]] a b
private def value05 (a b : Fin 4) : ℤ :=
  ![![11096759638118700, 11244498574852725, 9993397513585395, 9993397513585395], ![7557446336757135, 10775913399750135, 6566829955691460, 6566829955691460], ![8338750804328490, 8402425950908535, 6506579078494950, 7818210535321095], ![8338750804328490, 8402425950908535, 7818210535321095, 6506579078494950]] a b

private theorem assignment05 : ∀ (a b : Fin 4), 
    EJMTriangleCacheData.assignment (state05 a b).1 =
      trianglePartialAct (state05 a b).2 ((group0Partial a b) ∘ lhsTriangle 5) := by
  decide +kernel

private theorem lower05 : ∀ (a b : Fin 4), 
    (mkTriangle (state05 a b)).row.lower = value05 a b := by
  decide +kernel

private theorem bound05 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value05 (e 17) (e 18) ≤ triangleBlock F1 5 e := by
  have valid := triangle_from_assignment (state05 (e 17) (e 18)) ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 5)
    (assignment05 (e 17) (e 18))
  have compatible := compatible_project (group0Partial (e 17) (e 18)) e (lhsTriangle 5)
    (group0Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state05 (e 17) (e 18)))
    ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 5) (e ∘ lhsTriangle 5) valid compatible
  change (mkTriangle (state05 (e 17) (e 18))).row.lower ≤
    triangleBlock F1 5 e at bound
  rw [lower05 (e 17) (e 18)] at bound
  exact bound

private def state06 (c : Fin 4) : Fin 41294 × LocalSym :=
  ![(0, (6, 0)), (2, (6, 0)), (2, (6, 2)), (2, (6, 3))] c
private def value06 (c : Fin 4) : ℤ :=
  ![(-333398033381595), (-3842827060476495), (-3842827060476495), (-3842827060476495)] c

private theorem assignment06 : ∀ (c : Fin 4), 
    EJMTriangleCacheData.assignment (state06 c).1 =
      trianglePartialAct (state06 c).2 ((group1Partial c) ∘ lhsTriangle 6) := by
  decide +kernel

private theorem lower06 : ∀ (c : Fin 4), 
    (mkTriangle (state06 c)).row.lower = value06 c := by
  decide +kernel

private theorem bound06 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value06 (e 19) ≤ triangleBlock F1 6 e := by
  have valid := triangle_from_assignment (state06 (e 19)) ((group1Partial (e 19)) ∘ lhsTriangle 6)
    (assignment06 (e 19))
  have compatible := compatible_project (group1Partial (e 19)) e (lhsTriangle 6)
    (group1Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state06 (e 19)))
    ((group1Partial (e 19)) ∘ lhsTriangle 6) (e ∘ lhsTriangle 6) valid compatible
  change (mkTriangle (state06 (e 19))).row.lower ≤
    triangleBlock F1 6 e at bound
  rw [lower06 (e 19)] at bound
  exact bound

private def state07 (a : Fin 4) : Fin 41294 × LocalSym :=
  ![(1236, (0, 0)), (1239, (0, 0)), (1242, (0, 0)), (1242, (0, 1))] a
private def value07 (a : Fin 4) : ℤ :=
  ![6370619825206455, 3681851609011485, 3688719419124285, 3688719419124285] a

private theorem assignment07 : ∀ (a : Fin 4), 
    EJMTriangleCacheData.assignment (state07 a).1 =
      trianglePartialAct (state07 a).2 ((group2Partial a) ∘ lhsTriangle 7) := by
  decide +kernel

private theorem lower07 : ∀ (a : Fin 4), 
    (mkTriangle (state07 a)).row.lower = value07 a := by
  decide +kernel

private theorem bound07 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value07 (e 17) ≤ triangleBlock F1 7 e := by
  have valid := triangle_from_assignment (state07 (e 17)) ((group2Partial (e 17)) ∘ lhsTriangle 7)
    (assignment07 (e 17))
  have compatible := compatible_project (group2Partial (e 17)) e (lhsTriangle 7)
    (group2Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state07 (e 17)))
    ((group2Partial (e 17)) ∘ lhsTriangle 7) (e ∘ lhsTriangle 7) valid compatible
  change (mkTriangle (state07 (e 17))).row.lower ≤
    triangleBlock F1 7 e at bound
  rw [lower07 (e 17)] at bound
  exact bound

private def state08 : Fin 41294 × LocalSym :=
  (15219, (0, 0))
private def value08 : ℤ :=
  (-6261360113060325)

private theorem assignment08 : 
    EJMTriangleCacheData.assignment (state08).1 =
      trianglePartialAct (state08).2 ((prefixPartial 17 1040) ∘ lhsTriangle 8) := by
  decide +kernel

private theorem lower08 : 
    (mkTriangle (state08)).row.lower = value08 := by
  decide +kernel

private theorem bound08 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value08 ≤ triangleBlock F1 8 e := by
  have valid := triangle_from_assignment (state08) ((prefixPartial 17 1040) ∘ lhsTriangle 8)
    (assignment08)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsTriangle 8)
    hp
  have bound := triangle_valid_lower (mkTriangle (state08))
    ((prefixPartial 17 1040) ∘ lhsTriangle 8) (e ∘ lhsTriangle 8) valid compatible
  change (mkTriangle (state08)).row.lower ≤
    triangleBlock F1 8 e at bound
  rw [lower08] at bound
  exact bound

private def state09 (a b : Fin 4) : Fin 41294 × LocalSym :=
  ![![(0, (6, 0)), (2, (6, 0)), (2, (6, 2)), (2, (6, 3))], ![(2, (0, 0)), (20, (6, 0)), (23, (6, 0)), (23, (6, 1))], ![(2, (0, 2)), (23, (6, 2)), (20, (6, 2)), (23, (6, 4))], ![(2, (0, 3)), (23, (6, 3)), (23, (6, 5)), (20, (6, 3))]] a b
private def value09 (a b : Fin 4) : ℤ :=
  ![![(-333398033381595), (-3842827060476495), (-3842827060476495), (-3842827060476495)], ![(-3842827060476495), (-6757394161834680), (-6497698621579620), (-6497698621579620)], ![(-3842827060476495), (-6497698621579620), (-6757394161834680), (-6497698621579620)], ![(-3842827060476495), (-6497698621579620), (-6497698621579620), (-6757394161834680)]] a b

private theorem assignment09 : ∀ (a b : Fin 4), 
    EJMTriangleCacheData.assignment (state09 a b).1 =
      trianglePartialAct (state09 a b).2 ((group0Partial a b) ∘ lhsTriangle 9) := by
  decide +kernel

private theorem lower09 : ∀ (a b : Fin 4), 
    (mkTriangle (state09 a b)).row.lower = value09 a b := by
  decide +kernel

private theorem bound09 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value09 (e 17) (e 18) ≤ triangleBlock F1 9 e := by
  have valid := triangle_from_assignment (state09 (e 17) (e 18)) ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 9)
    (assignment09 (e 17) (e 18))
  have compatible := compatible_project (group0Partial (e 17) (e 18)) e (lhsTriangle 9)
    (group0Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state09 (e 17) (e 18)))
    ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 9) (e ∘ lhsTriangle 9) valid compatible
  change (mkTriangle (state09 (e 17) (e 18))).row.lower ≤
    triangleBlock F1 9 e at bound
  rw [lower09 (e 17) (e 18)] at bound
  exact bound

private def state10 (c : Fin 4) : Fin 41294 × LocalSym :=
  ![(1282, (1, 0)), (1530, (0, 0)), (1618, (0, 0)), (1618, (0, 1))] c
private def value10 (c : Fin 4) : ℤ :=
  ![11096759638118700, 11244498574852725, 9993397513585395, 9993397513585395] c

private theorem assignment10 : ∀ (c : Fin 4), 
    EJMTriangleCacheData.assignment (state10 c).1 =
      trianglePartialAct (state10 c).2 ((group1Partial c) ∘ lhsTriangle 10) := by
  decide +kernel

private theorem lower10 : ∀ (c : Fin 4), 
    (mkTriangle (state10 c)).row.lower = value10 c := by
  decide +kernel

private theorem bound10 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value10 (e 19) ≤ triangleBlock F1 10 e := by
  have valid := triangle_from_assignment (state10 (e 19)) ((group1Partial (e 19)) ∘ lhsTriangle 10)
    (assignment10 (e 19))
  have compatible := compatible_project (group1Partial (e 19)) e (lhsTriangle 10)
    (group1Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state10 (e 19)))
    ((group1Partial (e 19)) ∘ lhsTriangle 10) (e ∘ lhsTriangle 10) valid compatible
  change (mkTriangle (state10 (e 19))).row.lower ≤
    triangleBlock F1 10 e at bound
  rw [lower10 (e 19)] at bound
  exact bound

private def state11 (a : Fin 4) : Fin 41294 × LocalSym :=
  ![(1236, (6, 0)), (1282, (6, 0)), (1370, (6, 0)), (1370, (6, 1))] a
private def value11 (a : Fin 4) : ℤ :=
  ![6370619825206455, 11096759638118700, 5798533471801980, 5798533471801980] a

private theorem assignment11 : ∀ (a : Fin 4), 
    EJMTriangleCacheData.assignment (state11 a).1 =
      trianglePartialAct (state11 a).2 ((group2Partial a) ∘ lhsTriangle 11) := by
  decide +kernel

private theorem lower11 : ∀ (a : Fin 4), 
    (mkTriangle (state11 a)).row.lower = value11 a := by
  decide +kernel

private theorem bound11 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value11 (e 17) ≤ triangleBlock F1 11 e := by
  have valid := triangle_from_assignment (state11 (e 17)) ((group2Partial (e 17)) ∘ lhsTriangle 11)
    (assignment11 (e 17))
  have compatible := compatible_project (group2Partial (e 17)) e (lhsTriangle 11)
    (group2Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state11 (e 17)))
    ((group2Partial (e 17)) ∘ lhsTriangle 11) (e ∘ lhsTriangle 11) valid compatible
  change (mkTriangle (state11 (e 17))).row.lower ≤
    triangleBlock F1 11 e at bound
  rw [lower11 (e 17)] at bound
  exact bound

private def state12 (a : Fin 4) : Fin 41294 × LocalSym :=
  ![(26, (0, 0)), (1292, (0, 0)), (1402, (0, 2)), (1402, (0, 3))] a
private def value12 (a : Fin 4) : ℤ :=
  ![(-4039106876650755), 7557446336757135, 5419639815914415, 5419639815914415] a

private theorem assignment12 : ∀ (a : Fin 4), 
    EJMTriangleCacheData.assignment (state12 a).1 =
      trianglePartialAct (state12 a).2 ((group2Partial a) ∘ lhsTriangle 12) := by
  decide +kernel

private theorem lower12 : ∀ (a : Fin 4), 
    (mkTriangle (state12 a)).row.lower = value12 a := by
  decide +kernel

private theorem bound12 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value12 (e 17) ≤ triangleBlock F1 12 e := by
  have valid := triangle_from_assignment (state12 (e 17)) ((group2Partial (e 17)) ∘ lhsTriangle 12)
    (assignment12 (e 17))
  have compatible := compatible_project (group2Partial (e 17)) e (lhsTriangle 12)
    (group2Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state12 (e 17)))
    ((group2Partial (e 17)) ∘ lhsTriangle 12) (e ∘ lhsTriangle 12) valid compatible
  change (mkTriangle (state12 (e 17))).row.lower ≤
    triangleBlock F1 12 e at bound
  rw [lower12 (e 17)] at bound
  exact bound

private def state13 (c : Fin 4) : Fin 41294 × LocalSym :=
  ![(2, (6, 0)), (1282, (0, 0)), (1370, (0, 2)), (1370, (0, 3))] c
private def value13 (c : Fin 4) : ℤ :=
  ![(-3842827060476495), 11096759638118700, 5798533471801980, 5798533471801980] c

private theorem assignment13 : ∀ (c : Fin 4), 
    EJMTriangleCacheData.assignment (state13 c).1 =
      trianglePartialAct (state13 c).2 ((group1Partial c) ∘ lhsTriangle 13) := by
  decide +kernel

private theorem lower13 : ∀ (c : Fin 4), 
    (mkTriangle (state13 c)).row.lower = value13 c := by
  decide +kernel

private theorem bound13 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value13 (e 19) ≤ triangleBlock F1 13 e := by
  have valid := triangle_from_assignment (state13 (e 19)) ((group1Partial (e 19)) ∘ lhsTriangle 13)
    (assignment13 (e 19))
  have compatible := compatible_project (group1Partial (e 19)) e (lhsTriangle 13)
    (group1Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state13 (e 19)))
    ((group1Partial (e 19)) ∘ lhsTriangle 13) (e ∘ lhsTriangle 13) valid compatible
  change (mkTriangle (state13 (e 19))).row.lower ≤
    triangleBlock F1 13 e at bound
  rw [lower13 (e 19)] at bound
  exact bound

private def state14 (a b : Fin 4) : Fin 41294 × LocalSym :=
  ![![(2, (7, 0)), (1282, (1, 0)), (1370, (1, 2)), (1370, (1, 3))], ![(1239, (7, 0)), (631, (2, 6)), (3983, (2, 12)), (3983, (2, 13))], ![(1242, (7, 2)), (4422, (2, 14)), (1044, (7, 8)), (4547, (7, 17))], ![(1242, (7, 3)), (4422, (2, 15)), (4547, (7, 16)), (1044, (7, 9))]] a b
private def value14 (a b : Fin 4) : ℤ :=
  ![![(-3842827060476495), 11096759638118700, 5798533471801980, 5798533471801980], ![3681851609011485, 6805683703237965, 3990933291731295, 3990933291731295], ![3688719419124285, 4954118393486535, 4033680001408785, 3707204259170685], ![3688719419124285, 4954118393486535, 3707204259170685, 4033680001408785]] a b

private theorem assignment14 : ∀ (a b : Fin 4), 
    EJMTriangleCacheData.assignment (state14 a b).1 =
      trianglePartialAct (state14 a b).2 ((group0Partial a b) ∘ lhsTriangle 14) := by
  decide +kernel

private theorem lower14 : ∀ (a b : Fin 4), 
    (mkTriangle (state14 a b)).row.lower = value14 a b := by
  decide +kernel

private theorem bound14 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value14 (e 17) (e 18) ≤ triangleBlock F1 14 e := by
  have valid := triangle_from_assignment (state14 (e 17) (e 18)) ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 14)
    (assignment14 (e 17) (e 18))
  have compatible := compatible_project (group0Partial (e 17) (e 18)) e (lhsTriangle 14)
    (group0Compatible e hp)
  have bound := triangle_valid_lower (mkTriangle (state14 (e 17) (e 18)))
    ((group0Partial (e 17) (e 18)) ∘ lhsTriangle 14) (e ∘ lhsTriangle 14) valid compatible
  change (mkTriangle (state14 (e 17) (e 18))).row.lower ≤
    triangleBlock F1 14 e at bound
  rw [lower14 (e 17) (e 18)] at bound
  exact bound

private def state15 : Fin 41294 × LocalSym :=
  (26774, (0, 0))
private def value15 : ℤ :=
  (-333398033381595)

private theorem assignment15 : 
    EJMTriangleCacheData.assignment (state15).1 =
      trianglePartialAct (state15).2 ((prefixPartial 17 1040) ∘ lhsTriangle 15) := by
  decide +kernel

private theorem lower15 : 
    (mkTriangle (state15)).row.lower = value15 := by
  decide +kernel

private theorem bound15 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value15 ≤ triangleBlock F1 15 e := by
  have valid := triangle_from_assignment (state15) ((prefixPartial 17 1040) ∘ lhsTriangle 15)
    (assignment15)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsTriangle 15)
    hp
  have bound := triangle_valid_lower (mkTriangle (state15))
    ((prefixPartial 17 1040) ∘ lhsTriangle 15) (e ∘ lhsTriangle 15) valid compatible
  change (mkTriangle (state15)).row.lower ≤
    triangleBlock F1 15 e at bound
  rw [lower15] at bound
  exact bound

private def state16 : Fin 8689 × LocalSym :=
  (3696, (2, 0))
private def value16 : ℤ :=
  1600976283908820

private theorem assignment16 : 
    EJMSingletonCacheData.assignment (state16).1 =
      singletonPartialAct (state16).2 ((prefixPartial 17 1040) ∘ lhsSingleton 0) := by
  decide +kernel

private theorem lower16 : 
    (mkSingleton (state16)).row.lower = value16 := by
  decide +kernel

private theorem bound16 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value16 ≤ singletonBlock F2 0 e := by
  have valid := singleton_from_assignment (state16) ((prefixPartial 17 1040) ∘ lhsSingleton 0)
    (assignment16)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 0)
    hp
  have bound := singleton_valid_lower (mkSingleton (state16))
    ((prefixPartial 17 1040) ∘ lhsSingleton 0) (e ∘ lhsSingleton 0) valid compatible
  change (mkSingleton (state16)).row.lower ≤
    singletonBlock F2 0 e at bound
  rw [lower16] at bound
  exact bound

private def state17 : Fin 8689 × LocalSym :=
  (1234, (0, 0))
private def value17 : ℤ :=
  1600976283908820

private theorem assignment17 : 
    EJMSingletonCacheData.assignment (state17).1 =
      singletonPartialAct (state17).2 ((prefixPartial 17 1040) ∘ lhsSingleton 1) := by
  decide +kernel

private theorem lower17 : 
    (mkSingleton (state17)).row.lower = value17 := by
  decide +kernel

private theorem bound17 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value17 ≤ singletonBlock F2 1 e := by
  have valid := singleton_from_assignment (state17) ((prefixPartial 17 1040) ∘ lhsSingleton 1)
    (assignment17)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 1)
    hp
  have bound := singleton_valid_lower (mkSingleton (state17))
    ((prefixPartial 17 1040) ∘ lhsSingleton 1) (e ∘ lhsSingleton 1) valid compatible
  change (mkSingleton (state17)).row.lower ≤
    singletonBlock F2 1 e at bound
  rw [lower17] at bound
  exact bound

private def state18 : Fin 8689 × LocalSym :=
  (1234, (0, 0))
private def value18 : ℤ :=
  1600976283908820

private theorem assignment18 : 
    EJMSingletonCacheData.assignment (state18).1 =
      singletonPartialAct (state18).2 ((prefixPartial 17 1040) ∘ lhsSingleton 2) := by
  decide +kernel

private theorem lower18 : 
    (mkSingleton (state18)).row.lower = value18 := by
  decide +kernel

private theorem bound18 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value18 ≤ singletonBlock F2 2 e := by
  have valid := singleton_from_assignment (state18) ((prefixPartial 17 1040) ∘ lhsSingleton 2)
    (assignment18)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 2)
    hp
  have bound := singleton_valid_lower (mkSingleton (state18))
    ((prefixPartial 17 1040) ∘ lhsSingleton 2) (e ∘ lhsSingleton 2) valid compatible
  change (mkSingleton (state18)).row.lower ≤
    singletonBlock F2 2 e at bound
  rw [lower18] at bound
  exact bound

private def state19 : Fin 8689 × LocalSym :=
  (3696, (2, 0))
private def value19 : ℤ :=
  1600976283908820

private theorem assignment19 : 
    EJMSingletonCacheData.assignment (state19).1 =
      singletonPartialAct (state19).2 ((prefixPartial 17 1040) ∘ lhsSingleton 3) := by
  decide +kernel

private theorem lower19 : 
    (mkSingleton (state19)).row.lower = value19 := by
  decide +kernel

private theorem bound19 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value19 ≤ singletonBlock F2 3 e := by
  have valid := singleton_from_assignment (state19) ((prefixPartial 17 1040) ∘ lhsSingleton 3)
    (assignment19)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 3)
    hp
  have bound := singleton_valid_lower (mkSingleton (state19))
    ((prefixPartial 17 1040) ∘ lhsSingleton 3) (e ∘ lhsSingleton 3) valid compatible
  change (mkSingleton (state19)).row.lower ≤
    singletonBlock F2 3 e at bound
  rw [lower19] at bound
  exact bound

private def state20 : Fin 8689 × LocalSym :=
  (3643, (0, 0))
private def value20 : ℤ :=
  342684662906040

private theorem assignment20 : 
    EJMSingletonCacheData.assignment (state20).1 =
      singletonPartialAct (state20).2 ((prefixPartial 17 1040) ∘ lhsSingleton 4) := by
  decide +kernel

private theorem lower20 : 
    (mkSingleton (state20)).row.lower = value20 := by
  decide +kernel

private theorem bound20 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value20 ≤ singletonBlock F2 4 e := by
  have valid := singleton_from_assignment (state20) ((prefixPartial 17 1040) ∘ lhsSingleton 4)
    (assignment20)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 4)
    hp
  have bound := singleton_valid_lower (mkSingleton (state20))
    ((prefixPartial 17 1040) ∘ lhsSingleton 4) (e ∘ lhsSingleton 4) valid compatible
  change (mkSingleton (state20)).row.lower ≤
    singletonBlock F2 4 e at bound
  rw [lower20] at bound
  exact bound

private def state21 : Fin 8689 × LocalSym :=
  (1234, (0, 0))
private def value21 : ℤ :=
  1600976283908820

private theorem assignment21 : 
    EJMSingletonCacheData.assignment (state21).1 =
      singletonPartialAct (state21).2 ((prefixPartial 17 1040) ∘ lhsSingleton 5) := by
  decide +kernel

private theorem lower21 : 
    (mkSingleton (state21)).row.lower = value21 := by
  decide +kernel

private theorem bound21 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value21 ≤ singletonBlock F2 5 e := by
  have valid := singleton_from_assignment (state21) ((prefixPartial 17 1040) ∘ lhsSingleton 5)
    (assignment21)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 5)
    hp
  have bound := singleton_valid_lower (mkSingleton (state21))
    ((prefixPartial 17 1040) ∘ lhsSingleton 5) (e ∘ lhsSingleton 5) valid compatible
  change (mkSingleton (state21)).row.lower ≤
    singletonBlock F2 5 e at bound
  rw [lower21] at bound
  exact bound

private def state22 : Fin 8689 × LocalSym :=
  (3643, (0, 0))
private def value22 : ℤ :=
  342684662906040

private theorem assignment22 : 
    EJMSingletonCacheData.assignment (state22).1 =
      singletonPartialAct (state22).2 ((prefixPartial 17 1040) ∘ lhsSingleton 6) := by
  decide +kernel

private theorem lower22 : 
    (mkSingleton (state22)).row.lower = value22 := by
  decide +kernel

private theorem bound22 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value22 ≤ singletonBlock F2 6 e := by
  have valid := singleton_from_assignment (state22) ((prefixPartial 17 1040) ∘ lhsSingleton 6)
    (assignment22)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 6)
    hp
  have bound := singleton_valid_lower (mkSingleton (state22))
    ((prefixPartial 17 1040) ∘ lhsSingleton 6) (e ∘ lhsSingleton 6) valid compatible
  change (mkSingleton (state22)).row.lower ≤
    singletonBlock F2 6 e at bound
  rw [lower22] at bound
  exact bound

private def state23 : Fin 8689 × LocalSym :=
  (1983, (8, 6))
private def value23 : ℤ :=
  (-880826071055385)

private theorem assignment23 : 
    EJMSingletonCacheData.assignment (state23).1 =
      singletonPartialAct (state23).2 ((prefixPartial 17 1040) ∘ lhsSingleton 7) := by
  decide +kernel

private theorem lower23 : 
    (mkSingleton (state23)).row.lower = value23 := by
  decide +kernel

private theorem bound23 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value23 ≤ singletonBlock F2 7 e := by
  have valid := singleton_from_assignment (state23) ((prefixPartial 17 1040) ∘ lhsSingleton 7)
    (assignment23)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 7)
    hp
  have bound := singleton_valid_lower (mkSingleton (state23))
    ((prefixPartial 17 1040) ∘ lhsSingleton 7) (e ∘ lhsSingleton 7) valid compatible
  change (mkSingleton (state23)).row.lower ≤
    singletonBlock F2 7 e at bound
  rw [lower23] at bound
  exact bound

private def state24 : Fin 8689 × LocalSym :=
  (3696, (0, 0))
private def value24 : ℤ :=
  1600976283908820

private theorem assignment24 : 
    EJMSingletonCacheData.assignment (state24).1 =
      singletonPartialAct (state24).2 ((prefixPartial 17 1040) ∘ lhsSingleton 8) := by
  decide +kernel

private theorem lower24 : 
    (mkSingleton (state24)).row.lower = value24 := by
  decide +kernel

private theorem bound24 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value24 ≤ singletonBlock F2 8 e := by
  have valid := singleton_from_assignment (state24) ((prefixPartial 17 1040) ∘ lhsSingleton 8)
    (assignment24)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 8)
    hp
  have bound := singleton_valid_lower (mkSingleton (state24))
    ((prefixPartial 17 1040) ∘ lhsSingleton 8) (e ∘ lhsSingleton 8) valid compatible
  change (mkSingleton (state24)).row.lower ≤
    singletonBlock F2 8 e at bound
  rw [lower24] at bound
  exact bound

private def state25 : Fin 8689 × LocalSym :=
  (1200, (0, 0))
private def value25 : ℤ :=
  342684662906040

private theorem assignment25 : 
    EJMSingletonCacheData.assignment (state25).1 =
      singletonPartialAct (state25).2 ((prefixPartial 17 1040) ∘ lhsSingleton 9) := by
  decide +kernel

private theorem lower25 : 
    (mkSingleton (state25)).row.lower = value25 := by
  decide +kernel

private theorem bound25 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value25 ≤ singletonBlock F2 9 e := by
  have valid := singleton_from_assignment (state25) ((prefixPartial 17 1040) ∘ lhsSingleton 9)
    (assignment25)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 9)
    hp
  have bound := singleton_valid_lower (mkSingleton (state25))
    ((prefixPartial 17 1040) ∘ lhsSingleton 9) (e ∘ lhsSingleton 9) valid compatible
  change (mkSingleton (state25)).row.lower ≤
    singletonBlock F2 9 e at bound
  rw [lower25] at bound
  exact bound

private def state26 : Fin 8689 × LocalSym :=
  (4159, (8, 6))
private def value26 : ℤ :=
  (-1917671049571095)

private theorem assignment26 : 
    EJMSingletonCacheData.assignment (state26).1 =
      singletonPartialAct (state26).2 ((prefixPartial 17 1040) ∘ lhsSingleton 10) := by
  decide +kernel

private theorem lower26 : 
    (mkSingleton (state26)).row.lower = value26 := by
  decide +kernel

private theorem bound26 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value26 ≤ singletonBlock F2 10 e := by
  have valid := singleton_from_assignment (state26) ((prefixPartial 17 1040) ∘ lhsSingleton 10)
    (assignment26)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 10)
    hp
  have bound := singleton_valid_lower (mkSingleton (state26))
    ((prefixPartial 17 1040) ∘ lhsSingleton 10) (e ∘ lhsSingleton 10) valid compatible
  change (mkSingleton (state26)).row.lower ≤
    singletonBlock F2 10 e at bound
  rw [lower26] at bound
  exact bound

private def state27 : Fin 8689 × LocalSym :=
  (1200, (0, 0))
private def value27 : ℤ :=
  342684662906040

private theorem assignment27 : 
    EJMSingletonCacheData.assignment (state27).1 =
      singletonPartialAct (state27).2 ((prefixPartial 17 1040) ∘ lhsSingleton 11) := by
  decide +kernel

private theorem lower27 : 
    (mkSingleton (state27)).row.lower = value27 := by
  decide +kernel

private theorem bound27 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value27 ≤ singletonBlock F2 11 e := by
  have valid := singleton_from_assignment (state27) ((prefixPartial 17 1040) ∘ lhsSingleton 11)
    (assignment27)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 11)
    hp
  have bound := singleton_valid_lower (mkSingleton (state27))
    ((prefixPartial 17 1040) ∘ lhsSingleton 11) (e ∘ lhsSingleton 11) valid compatible
  change (mkSingleton (state27)).row.lower ≤
    singletonBlock F2 11 e at bound
  rw [lower27] at bound
  exact bound

private def state28 : Fin 8689 × LocalSym :=
  (4, (1, 0))
private def value28 : ℤ :=
  1693600988588145

private theorem assignment28 : 
    EJMSingletonCacheData.assignment (state28).1 =
      singletonPartialAct (state28).2 ((prefixPartial 17 1040) ∘ lhsSingleton 12) := by
  decide +kernel

private theorem lower28 : 
    (mkSingleton (state28)).row.lower = value28 := by
  decide +kernel

private theorem bound28 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value28 ≤ singletonBlock F2 12 e := by
  have valid := singleton_from_assignment (state28) ((prefixPartial 17 1040) ∘ lhsSingleton 12)
    (assignment28)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 12)
    hp
  have bound := singleton_valid_lower (mkSingleton (state28))
    ((prefixPartial 17 1040) ∘ lhsSingleton 12) (e ∘ lhsSingleton 12) valid compatible
  change (mkSingleton (state28)).row.lower ≤
    singletonBlock F2 12 e at bound
  rw [lower28] at bound
  exact bound

private def state29 (a : Fin 4) : Fin 8689 × LocalSym :=
  ![(4, (0, 0)), (497, (10, 6)), (953, (0, 8)), (953, (0, 9))] a
private def value29 (a : Fin 4) : ℤ :=
  ![1693600988588145, (-594470238080355), (-549565382241330), (-549565382241330)] a

private theorem assignment29 : ∀ (a : Fin 4), 
    EJMSingletonCacheData.assignment (state29 a).1 =
      singletonPartialAct (state29 a).2 ((group2Partial a) ∘ lhsSingleton 13) := by
  decide +kernel

private theorem lower29 : ∀ (a : Fin 4), 
    (mkSingleton (state29 a)).row.lower = value29 a := by
  decide +kernel

private theorem bound29 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value29 (e 17) ≤ singletonBlock F2 13 e := by
  have valid := singleton_from_assignment (state29 (e 17)) ((group2Partial (e 17)) ∘ lhsSingleton 13)
    (assignment29 (e 17))
  have compatible := compatible_project (group2Partial (e 17)) e (lhsSingleton 13)
    (group2Compatible e hp)
  have bound := singleton_valid_lower (mkSingleton (state29 (e 17)))
    ((group2Partial (e 17)) ∘ lhsSingleton 13) (e ∘ lhsSingleton 13) valid compatible
  change (mkSingleton (state29 (e 17))).row.lower ≤
    singletonBlock F2 13 e at bound
  rw [lower29 (e 17)] at bound
  exact bound

private def state30 : Fin 8689 × LocalSym :=
  (3301, (1, 0))
private def value30 : ℤ :=
  (-594470238080355)

private theorem assignment30 : 
    EJMSingletonCacheData.assignment (state30).1 =
      singletonPartialAct (state30).2 ((prefixPartial 17 1040) ∘ lhsSingleton 14) := by
  decide +kernel

private theorem lower30 : 
    (mkSingleton (state30)).row.lower = value30 := by
  decide +kernel

private theorem bound30 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value30 ≤ singletonBlock F2 14 e := by
  have valid := singleton_from_assignment (state30) ((prefixPartial 17 1040) ∘ lhsSingleton 14)
    (assignment30)
  have compatible := compatible_project (prefixPartial 17 1040) e (lhsSingleton 14)
    hp
  have bound := singleton_valid_lower (mkSingleton (state30))
    ((prefixPartial 17 1040) ∘ lhsSingleton 14) (e ∘ lhsSingleton 14) valid compatible
  change (mkSingleton (state30)).row.lower ≤
    singletonBlock F2 14 e at bound
  rw [lower30] at bound
  exact bound

private def state31 (c : Fin 4) : Fin 8689 × LocalSym :=
  ![(4, (0, 0)), (497, (10, 6)), (953, (0, 8)), (953, (0, 9))] c
private def value31 (c : Fin 4) : ℤ :=
  ![1693600988588145, (-594470238080355), (-549565382241330), (-549565382241330)] c

private theorem assignment31 : ∀ (c : Fin 4), 
    EJMSingletonCacheData.assignment (state31 c).1 =
      singletonPartialAct (state31 c).2 ((group1Partial c) ∘ lhsSingleton 15) := by
  decide +kernel

private theorem lower31 : ∀ (c : Fin 4), 
    (mkSingleton (state31 c)).row.lower = value31 c := by
  decide +kernel

private theorem bound31 (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    value31 (e 19) ≤ singletonBlock F2 15 e := by
  have valid := singleton_from_assignment (state31 (e 19)) ((group1Partial (e 19)) ∘ lhsSingleton 15)
    (assignment31 (e 19))
  have compatible := compatible_project (group1Partial (e 19)) e (lhsSingleton 15)
    (group1Compatible e hp)
  have bound := singleton_valid_lower (mkSingleton (state31 (e 19)))
    ((group1Partial (e 19)) ∘ lhsSingleton 15) (e ∘ lhsSingleton 15) valid compatible
  change (mkSingleton (state31 (e 19))).row.lower ≤
    singletonBlock F2 15 e at bound
  rw [lower31 (e 19)] at bound
  exact bound

set_option trace.profiler true in
private theorem group0Minimum : ∀ (a b : Fin 4),
    (-1780304708546910 : ℤ) ≤ value01 a b + value05 a b + value09 a b + value14 a b := by
  decide +kernel

set_option trace.profiler true in
private theorem group1Minimum : ∀ (c : Fin 4),
    (4771308472372260 : ℤ) ≤ value02 c + value06 c + value10 c + value13 c + value31 c := by
  decide +kernel

set_option trace.profiler true in
private theorem group2Minimum : ∀ (a : Fin 4),
    (10062335728968705 : ℤ) ≤ value03 a + value07 a + value11 a + value12 a + value29 a := by
  decide +kernel

private def triangleLower (a b c : Fin 4) : Fin 16 → ℤ :=
  ![value00, value01 a b, value02 c, value03 a, value04, value05 a b, value06 c, value07 a, value08, value09 a b, value10 c, value11 a, value12 a, value13 c, value14 a b, value15]

private theorem triangleLower_bounds (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    ∀ k, triangleLower (e 17) (e 18) (e 19) k ≤
      triangleBlock F1 k e := by
  intro k
  fin_cases k
  · exact bound00 e hp
  · exact bound01 e hp
  · exact bound02 e hp
  · exact bound03 e hp
  · exact bound04 e hp
  · exact bound05 e hp
  · exact bound06 e hp
  · exact bound07 e hp
  · exact bound08 e hp
  · exact bound09 e hp
  · exact bound10 e hp
  · exact bound11 e hp
  · exact bound12 e hp
  · exact bound13 e hp
  · exact bound14 e hp
  · exact bound15 e hp

private def singletonLower (a b c : Fin 4) : Fin 16 → ℤ :=
  ![value16, value17, value18, value19, value20, value21, value22, value23, value24, value25, value26, value27, value28, value29 a, value30, value31 c]

private theorem singletonLower_bounds (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 17 1040) e) :
    ∀ k, singletonLower (e 17) (e 18) (e 19) k ≤
      singletonBlock F2 k e := by
  intro k
  fin_cases k
  · exact bound16 e hp
  · exact bound17 e hp
  · exact bound18 e hp
  · exact bound19 e hp
  · exact bound20 e hp
  · exact bound21 e hp
  · exact bound22 e hp
  · exact bound23 e hp
  · exact bound24 e hp
  · exact bound25 e hp
  · exact bound26 e hp
  · exact bound27 e hp
  · exact bound28 e hp
  · exact bound29 e hp
  · exact bound30 e hp
  · exact bound31 e hp

set_option trace.profiler true in
theorem actual_prefix_score_lower_bound :
    ∀ e : Event (Fin 20) (Fin 4), Compatible (prefixPartial 17 1040) e →
      (6987435 : ℤ) ≤ score F1 F2 e := by
  intro e hp
  have ht : (∑ k : Fin 16, triangleLower (e 17) (e 18) (e 19) k) ≤
      ∑ k : Fin 16, triangleBlock F1 k e := by
    apply Finset.sum_le_sum
    intro k _
    exact triangleLower_bounds e hp k
  have hs : (∑ k : Fin 16, singletonLower (e 17) (e 18) (e 19) k) ≤
      ∑ k : Fin 16, singletonBlock F2 k e := by
    apply Finset.sum_le_sum
    intro k _
    exact singletonLower_bounds e hp k
  have numeric : (6987435 : ℤ) ≤
      (∑ k : Fin 16, triangleLower (e 17) (e 18) (e 19) k) +
        ∑ k : Fin 16, singletonLower (e 17) (e 18) (e 19) k := by
    have group0 := group0Minimum (e 17) (e 18)
    have group1 := group1Minimum (e 19)
    have group2 := group2Minimum (e 17)
    simp only [triangleLower, singletonLower, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    dsimp only [value00, value04, value08, value15, value16, value17, value18, value19, value20, value21, value22, value23, value24, value25, value26, value27, value28, value30]
    omega
  exact numeric.trans (add_le_add ht hs)

#print axioms actual_prefix_score_lower_bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMScopedMinCandidate171040
