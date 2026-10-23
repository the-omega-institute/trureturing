/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportAveragedCut
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalSupportAveragedCut
   mirror-E: none(waiver:original-support-orbit-cut)
   anchors: []
   utility: none
   digest: Averaging the original three-factor conflict forces a weighted outside count across all thirty-two original factors. -/

import D5.S3.Quantum.Entanglement.EJM.EJMOriginalSupportConflict
import D5.S3.Quantum.Entanglement.EJM.EJMSourceActionClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalSupportAveragedCut

open D5.S0.Certificates.FiniteNaturalJoin
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation (Node)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (trianglePerm singletonPerm)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalSupportConflict
open D5.S3.Quantum.Entanglement.EJM.EJMSourceActionClosure
open scoped BigOperators

def TriangleInside (e : Node → Fin 4) (i : Fin 16) : Prop :=
  List.ofFn (e ∘ lhsTriangle i) ∈ triangleSupport

def SingletonInside (e : Node → Fin 4) (i : Fin 16) : Prop :=
  List.ofFn (e ∘ lhsSingleton i) ∈ singletonSupport

instance (e : Node → Fin 4) (i : Fin 16) : Decidable (TriangleInside e i) :=
  inferInstanceAs (Decidable (_ ∈ triangleSupport))

instance (e : Node → Fin 4) (i : Fin 16) : Decidable (SingletonInside e i) :=
  inferInstanceAs (Decidable (_ ∈ singletonSupport))

/-- The indicator retains every actual local coordinate and all four outcomes. -/
def triangleOutside (e : Node → Fin 4) (i : Fin 16) : ℤ :=
  if TriangleInside e i then 0 else 1

def singletonOutside (e : Node → Fin 4) (i : Fin 16) : ℤ :=
  if SingletonInside e i then 0 else 1

private theorem covers_of_local {n : ℕ} (nodes : Fin n → Node)
    (rows : List (List (Fin 4))) (e : Node → Fin 4)
    (h : List.ofFn (e ∘ nodes) ∈ rows) :
    Covers (rows.map fun row => (List.ofFn nodes).zip row) e := by
  refine ⟨(List.ofFn nodes).zip (List.ofFn (e ∘ nodes)),
    List.mem_map.mpr ⟨_, h, rfl⟩, ?_⟩
  have he : List.ofFn (e ∘ nodes) = (List.ofFn nodes).map e :=
    List.map_ofFn.symm
  rw [he, ← List.map_prod_left_eq_zip]
  intro cv hcv
  rcases List.mem_map.mp hcv with ⟨c, _, rfl⟩
  rfl

set_option maxHeartbeats 4000000 in
-- Check only 12 actions on the actual 132 support rows, not all 4^10 local events.
private theorem triangle_support_coordinate (k : Fin 12) (e : Fin 10 → Fin 4)
    (h : List.ofFn e ∈ triangleSupport) :
    List.ofFn (e ∘ trianglePerm k) ∈ triangleSupport := by
  have checked : ∀ k : Fin 12, ∀ row ∈ triangleSupport,
      List.ofFn (fun j : Fin 10 => row[(trianglePerm k j).val]?.getD 0)
        ∈ triangleSupport := by decide
  simpa only [List.getElem?_ofFn, Fin.is_lt, dif_pos, Option.getD_some,
    Function.comp_def] using checked k (List.ofFn e) h

set_option maxHeartbeats 4000000 in
-- Check all 12 actions on the actual 168 singleton rows with no outcome normalization.
private theorem singleton_support_coordinate (k : Fin 12) (e : Fin 9 → Fin 4)
    (h : List.ofFn e ∈ singletonSupport) :
    List.ofFn (e ∘ singletonPerm k) ∈ singletonSupport := by
  have checked : ∀ k : Fin 12, ∀ row ∈ singletonSupport,
      List.ofFn (fun j : Fin 9 => row[(singletonPerm k j).val]?.getD 0)
        ∈ singletonSupport := by decide
  simpa only [List.getElem?_ofFn, Fin.is_lt, dif_pos, Option.getD_some,
    Function.comp_def] using checked k (List.ofFn e) h

private theorem triangle_inside_source (e : Node → Fin 4) (s : Fin 192)
    (i : Fin 16) (h : TriangleInside e (triangleIndex s i)) :
    TriangleInside (e ∘ sourceSymmetry s) i := by
  unfold TriangleInside at *
  rw [Function.comp_assoc, triangle_map_closure, ← Function.comp_assoc]
  exact triangle_support_coordinate _ _ h

private theorem singleton_inside_source (e : Node → Fin 4) (s : Fin 192)
    (i : Fin 16) (h : SingletonInside e (singletonIndex s i)) :
    SingletonInside (e ∘ sourceSymmetry s) i := by
  unfold SingletonInside at *
  rw [Function.comp_assoc, singleton_map_closure, ← Function.comp_assoc]
  exact singleton_support_coordinate _ _ h

private theorem each_source_outside (e : Node → Fin 4) (s : Fin 192) :
    1 ≤ triangleOutside e (triangleIndex s 2) +
      triangleOutside e (triangleIndex s 3) +
      singletonOutside e (singletonIndex s 8) := by
  by_cases ht2 : TriangleInside e (triangleIndex s 2)
  · by_cases ht3 : TriangleInside e (triangleIndex s 3)
    · by_cases hs : SingletonInside e (singletonIndex s 8)
      · exfalso
        exact result ⟨e ∘ sourceSymmetry s,
          covers_of_local _ _ _ (singleton_inside_source e s 8 hs),
          covers_of_local _ _ _ (triangle_inside_source e s 2 ht2),
          covers_of_local _ _ _ (triangle_inside_source e s 3 ht3)⟩
      · simp [triangleOutside, singletonOutside, ht2, ht3, hs]
    · simp [triangleOutside, singletonOutside, ht2, ht3]
      split_ifs <;> norm_num
  · simp [triangleOutside, singletonOutside, ht2]
    split_ifs <;> norm_num

private theorem balanced_sum (index : Fin 192 → Fin 16)
    (multiplicity : ∀ i : Fin 16,
      (Finset.univ.filter fun s => index s = i).card = 12)
    (f : Fin 16 → ℤ) :
    (∑ s : Fin 192, f (index s)) = 12 * ∑ i : Fin 16, f i := by
  rw [← Finset.sum_fiberwise' Finset.univ index f]
  simp only [Finset.sum_const, multiplicity, nsmul_eq_mul]
  rw [Finset.mul_sum]
  norm_num

set_option maxHeartbeats 4000000 in
-- The kernel checks 192 original marginal-index transports and all sixteen fibers.
private theorem original_multiplicities :
    (∀ i : Fin 16,
      (Finset.univ.filter fun s : Fin 192 => triangleIndex s 2 = i).card = 12) ∧
    (∀ i : Fin 16,
      (Finset.univ.filter fun s : Fin 192 => triangleIndex s 3 = i).card = 12) ∧
    (∀ i : Fin 16,
      (Finset.univ.filter fun s : Fin 192 => singletonIndex s 8 = i).card = 12) := by
  decide

/-- The original full supports obey a cut on all 32 factors. This is an outside
count and carries no unproved positive lower bound for the original EJM score. -/
theorem averaged_outside_cut (e : Node → Fin 4) :
    16 ≤ 2 * (∑ i : Fin 16, triangleOutside e i) +
      ∑ i : Fin 16, singletonOutside e i := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun s _ => each_source_outside e s)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  rw [balanced_sum _ original_multiplicities.1,
    balanced_sum _ original_multiplicities.2.1,
    balanced_sum _ original_multiplicities.2.2] at h
  omega

#print axioms averaged_outside_cut

end D5.S3.Quantum.Entanglement.EJM.EJMOriginalSupportAveragedCut
