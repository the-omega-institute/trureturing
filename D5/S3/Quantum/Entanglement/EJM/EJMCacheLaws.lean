/- GID: D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMCacheLaws
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: none
   digest: Actual local inverse, composition, update and original block-incidence laws preserve full cache association. -/

/- Prepared source, not compiled. These are proofs of actual function laws,
not producer assertions. The cache receipts and complete actual replay must
still be kernel accepted as part of the same full certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCacheLaws
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym outcome)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
open D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open D5.S3.Quantum.Entanglement.EJMInflationScore

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem triangle_inverse_receipt : ∀ s : Fin 12, ∀ i : Fin 10,
    trianglePerm (coordinateInverse s) (trianglePerm s i) = i ∧
    trianglePerm s (trianglePerm (coordinateInverse s) i) = i := by
  decide +kernel

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem singleton_inverse_receipt : ∀ s : Fin 12, ∀ i : Fin 9,
    singletonPerm (coordinateInverse s) (singletonPerm s i) = i ∧
    singletonPerm s (singletonPerm (coordinateInverse s) i) = i := by
  decide +kernel

theorem triangle_coordinate_injective (s : Fin 12) : Function.Injective (trianglePerm s) := by
  intro i j h
  have hh := congrArg (trianglePerm (coordinateInverse s)) h
  simpa only [(triangle_inverse_receipt s i).1,
    (triangle_inverse_receipt s j).1] using hh

theorem singleton_coordinate_injective (s : Fin 12) : Function.Injective (singletonPerm s) := by
  intro i j h
  have hh := congrArg (singletonPerm (coordinateInverse s)) h
  simpa only [(singleton_inverse_receipt s i).1,
    (singleton_inverse_receipt s j).1] using hh

theorem triangle_preimage_apply (s : LocalSym) (i : Fin 10) :
    trianglePerm s.1 (trianglePreimage s i) = i :=
  (triangle_inverse_receipt s.1 i).2

theorem singleton_preimage_apply (s : LocalSym) (i : Fin 9) :
    singletonPerm s.1 (singletonPreimage s i) = i :=
  (singleton_inverse_receipt s.1 i).2

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem triangle_mul_receipt : ∀ s t : Fin 12,
    trianglePerm s ∘ trianglePerm t = trianglePerm (triangleMul s t) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem singleton_mul_receipt : ∀ s t : Fin 12,
    singletonPerm s ∘ singletonPerm t = singletonPerm (singletonMul s t) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem outcome_mul_receipt : ∀ t s : Fin 24,
    outcome t ∘ outcome s = outcome (outcomeMul t s) := by
  decide +kernel

private theorem partial_comp {n : ℕ} (ct cs : Fin n → Fin n)
    (ot os : Fin 4 → Fin 4) (p : Partial (Fin n) (Fin 4)) :
    partialAct ct ot (partialAct cs os p) = partialAct (cs ∘ ct) (ot ∘ os) p := by
  funext i
  simp only [partialAct, Function.comp_apply, Option.map_map]

theorem triangle_compose (t s : LocalSym) (p : Partial (Fin 10) (Fin 4)) :
    trianglePartialAct t (trianglePartialAct s p) =
      trianglePartialAct (triangleCompose t s) p := by
  change partialAct (trianglePerm t.1) (outcome t.2)
    (partialAct (trianglePerm s.1) (outcome s.2) p) =
    partialAct (trianglePerm (triangleMul s.1 t.1)) (outcome (outcomeMul t.2 s.2)) p
  rw [partial_comp, triangle_mul_receipt, outcome_mul_receipt]

theorem singleton_compose (t s : LocalSym) (p : Partial (Fin 9) (Fin 4)) :
    singletonPartialAct t (singletonPartialAct s p) =
      singletonPartialAct (singletonCompose t s) p := by
  change partialAct (singletonPerm t.1) (outcome t.2)
    (partialAct (singletonPerm s.1) (outcome s.2) p) =
    partialAct (singletonPerm (singletonMul s.1 t.1)) (outcome (outcomeMul t.2 s.2)) p
  rw [partial_comp, singleton_mul_receipt, outcome_mul_receipt]

private theorem partial_update {n : ℕ} (coordinate preimage : Fin n → Fin n)
    (relabel : Fin 4 → Fin 4) (injective : Function.Injective coordinate)
    (rightInverse : ∀ i, coordinate (preimage i) = i)
    (p : Partial (Fin n) (Fin 4)) (i : Fin n) (a : Fin 4) :
    partialAct coordinate relabel (Function.update p i (some a)) =
      Function.update (partialAct coordinate relabel p) (preimage i) (some (relabel a)) := by
  funext j
  by_cases same : j = preimage i
  · subst j
    simp only [partialAct, rightInverse, Function.update_self, Option.map_some]
  · have different : coordinate j ≠ i := by
      intro equal
      apply same
      apply injective
      exact equal.trans (rightInverse i).symm
    simp only [partialAct, Function.update_of_ne different, Function.update_of_ne same]

theorem triangle_update (s : LocalSym) (p : Partial (Fin 10) (Fin 4))
    (i : Fin 10) (a : Fin 4) :
    trianglePartialAct s (Function.update p i (some a)) =
      Function.update (trianglePartialAct s p) (trianglePreimage s i) (some (outcome s.2 a)) :=
  partial_update _ _ _ (triangle_coordinate_injective s.1) (triangle_preimage_apply s) p i a

theorem singleton_update (s : LocalSym) (p : Partial (Fin 9) (Fin 4))
    (i : Fin 9) (a : Fin 4) :
    singletonPartialAct s (Function.update p i (some a)) =
      Function.update (singletonPartialAct s p) (singletonPreimage s i) (some (outcome s.2 a)) :=
  partial_update _ _ _ (singleton_coordinate_injective s.1) (singleton_preimage_apply s) p i a

theorem triangle_unknown (s : LocalSym) (p : Partial (Fin 10) (Fin 4))
    (i : Fin 10) (unknown : p i = none) :
    trianglePartialAct s p (trianglePreimage s i) = none := by
  change (p (trianglePerm s.1 (trianglePreimage s i))).map (outcome s.2) = none
  rw [triangle_preimage_apply, unknown]
  rfl

theorem singleton_unknown (s : LocalSym) (p : Partial (Fin 9) (Fin 4))
    (i : Fin 9) (unknown : p i = none) :
    singletonPartialAct s p (singletonPreimage s i) = none := by
  change (p (singletonPerm s.1 (singletonPreimage s i))).map (outcome s.2) = none
  rw [singleton_preimage_apply, unknown]
  rfl

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem triangle_incidence_receipt :
    (∀ (g : Fin 20) (k : Fin 16) (i : Fin 10),
      triangleIncidence g k = some i → lhsTriangle k i = g) ∧
    (∀ (g : Fin 20) (k : Fin 16),
      triangleIncidence g k = none → ∀ i, lhsTriangle k i ≠ g) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
-- This finite kernel receipt exhausts its explicit concrete domain; no producer premise is used.
private theorem singleton_incidence_receipt :
    (∀ (g : Fin 20) (k : Fin 16) (i : Fin 9),
      singletonIncidence g k = some i → lhsSingleton k i = g) ∧
    (∀ (g : Fin 20) (k : Fin 16),
      singletonIncidence g k = none → ∀ i, lhsSingleton k i ≠ g) := by
  decide +kernel

theorem triangle_incidence_some (g : Fin 20) (k : Fin 16) (i : Fin 10)
    (incidence : triangleIncidence g k = some i) : lhsTriangle k i = g := by
  exact triangle_incidence_receipt.1 g k i incidence

theorem singleton_incidence_some (g : Fin 20) (k : Fin 16) (i : Fin 9)
    (incidence : singletonIncidence g k = some i) : lhsSingleton k i = g := by
  exact singleton_incidence_receipt.1 g k i incidence

theorem triangle_projection_update (p : Partial (Fin 20) (Fin 4)) (g : Fin 20)
    (a : Fin 4) (k : Fin 16) :
    Function.update p g (some a) ∘ lhsTriangle k =
      match triangleIncidence g k with
      | none => p ∘ lhsTriangle k
      | some i => Function.update (p ∘ lhsTriangle k) i (some a) := by
  cases incidence : triangleIncidence g k with
  | none =>
    exact Function.update_comp_eq_of_forall_ne p (some a)
      (triangle_incidence_receipt.2 g k incidence)
  | some i =>
    have h := triangle_incidence_receipt.1 g k i incidence
    rw [← h]
    exact Function.update_comp_eq_of_injective p (triangle_injective k) i (some a)

theorem singleton_projection_update (p : Partial (Fin 20) (Fin 4)) (g : Fin 20)
    (a : Fin 4) (k : Fin 16) :
    Function.update p g (some a) ∘ lhsSingleton k =
      match singletonIncidence g k with
      | none => p ∘ lhsSingleton k
      | some i => Function.update (p ∘ lhsSingleton k) i (some a) := by
  cases incidence : singletonIncidence g k with
  | none =>
    exact Function.update_comp_eq_of_forall_ne p (some a)
      (singleton_incidence_receipt.2 g k incidence)
  | some i =>
    have h := singleton_incidence_receipt.1 g k i incidence
    rw [← h]
    exact Function.update_comp_eq_of_injective p (singleton_injective k) i (some a)

#print axioms triangle_compose
#print axioms singleton_compose
#print axioms triangle_update
#print axioms singleton_update
#print axioms triangle_projection_update
#print axioms singleton_projection_update

end D5.S3.Quantum.Entanglement.EJM.EJMCacheLaws
