/- GID: D5/S3/VertexAlgebra/Sectors/VBKMVirasoroBootstrap
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/VBKMVirasoroBootstrap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Virasoro and Borcherds presentation, action, and ideal structure. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap.positive_brackets_from_mixed
Direct frozen dependencies: none; all D5 prerequisites are in this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30339
Definitions are labelled bind-only as encodings, not as proofs of new propositions.
Declarations (consumer names are qualified by their owning module):
defect_bracket: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMVirasoroBootstrap.positive_brackets_from_mixed.
cyclic_operator_zero: proof_shape: content; frozen: none; escape_witness: VBKMVirasoroBootstrap.cyclic_operator_zero; consumers: VBKMVirasoroBootstrap.positive_brackets_from_mixed.
positive_brackets_from_mixed: proof_shape: content; frozen: none; escape_witness: VBKMVirasoroBootstrap.positive_brackets_from_mixed; consumers: VBKMRecursiveAction.qmode_positive_brackets.
full_brackets_from_mixed: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMRecursiveAction.qmode_virasoro.
-/


import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing
universe u v
namespace D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap

private theorem defect_bracket {A : Type*} [LieRing A] [LieAlgebra ℂ A]
    (x y z a : A) (c : ℂ) :
    ⁅⁅x,y⁆-c • z,a⁆ = ⁅x,⁅y,a⁆⁆-⁅y,⁅x,a⁆⁆-c • ⁅z,a⁆ := by
  rw [sub_lie,smul_lie,lie_lie]

variable {M I : Type*} [AddCommGroup M] [Module ℂ M]

private theorem cyclic_operator_zero (F : I → Module.End ℂ M) (v : M)
    (hspan : Submodule.span ℂ (Set.range (List.foldr (fun i x => F i x) v)) = ⊤)
    (D : Module.End ℂ M) (hDv : D v = 0) (hDF : ∀ i, ⁅D,F i⁆ = 0) : D = 0 := by
  have hw (w : List I) : D (List.foldr (fun i x => F i x) v w) = 0 := by
    induction w with
    | nil => exact hDv
    | cons i w ih =>
      have hh := LinearMap.congr_fun (hDF i) (List.foldr (fun i x => F i x) v w)
      change D (F i (List.foldr (fun i x => F i x) v w)) - F i (D (List.foldr (fun i x => F i x) v w)) = 0 at hh
      simpa [List.foldr_cons,ih] using hh
  have hker : Submodule.span ℂ (Set.range (List.foldr (fun i x => F i x) v)) ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    rintro x ⟨w,rfl⟩
    exact hw w
  rw [hspan] at hker
  apply LinearMap.ext
  intro x
  exact hker (Submodule.mem_top)

theorem positive_brackets_from_mixed (F : (I ⊕ ℕ+) → Module.End ℂ M) (v : M)
    (hspan : Submodule.span ℂ (Set.range (List.foldr (fun i x => F i x) v)) = ⊤)
    (T : ℤ → Module.End ℂ M) (C : Module.End ℂ M)
    (hnegative : ∀ r : ℕ+, T (-(r.val : ℤ)) = F (.inr r))
    (hroot : ∀ (m : ℤ), 0 < m → ∀ i : I, ⁅T m,F (.inl i)⁆ = 0)
    (hmixed : ∀ (m : ℤ) (r : ℕ+), ⁅T m,T (-(r.val : ℤ))⁆ =
      ((m+(r.val : ℤ) : ℤ) : ℂ) • T (m-r.val) +
      if m = r.val then ((m^3-m : ℤ) : ℂ) • C else 0)
    (hzero : ∀ m : ℤ, ⁅T m,T 0⁆ = (m : ℂ) • T m)
    (hcentral : ∀ m : ℤ, ⁅T m,C⁆ = 0)
    (hv : ∀ (m : ℤ), 0 < m → T m v = 0) :
    ∀ (m n : ℤ), 0 < m → 0 < n → ⁅T m,T n⁆ = ((m-n : ℤ) : ℂ) • T (m+n) := by
  have hall (k : ℕ) : ∀ (m n : ℤ), 0 < m → 0 < n → (m+n).toNat = k →
      ⁅T m,T n⁆ = ((m-n : ℤ) : ℂ) • T (m+n) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m n hm hn hk
      have hsmall (a b c : ℤ) (ha : 0 < a) (hc : 0 < c) (hsum : a+c = m+n)
          (hb : b < c) :
          ⁅T a,T b⁆ = ((a-b : ℤ) : ℂ) • T (a+b) +
            if a = -b then ((a^3-a : ℤ) : ℂ) • C else 0 := by
        by_cases hbpos : 0 < b
        · have hlt : (a+b).toNat < k := by omega
          rw [ih (a+b).toNat hlt a b ha hbpos rfl]
          rw [if_neg (by omega),add_zero]
        · by_cases hb0 : b = 0
          · subst b
            simpa [ne_of_gt ha] using hzero a
          · let r : ℕ+ := ⟨(-b).toNat,by omega⟩
            have hr : (r.val : ℤ) = -b := by
              dsimp [r]
              rw [Int.toNat_of_nonneg (by omega)]
            have hh := hmixed a r
            simpa [hr,sub_eq_add_neg] using hh
      let D : Module.End ℂ M := ⁅T m,T n⁆ - ((m-n : ℤ) : ℂ) • T (m+n)
      have hDv : D v = 0 := by
        change (T m (T n v)-T n (T m v))-((m-n : ℤ) : ℂ) • T (m+n) v = 0
        simp [hv m hm,hv n hn,hv (m+n) (by omega)]
      have hDF : ∀ g : I ⊕ ℕ+, ⁅D,F g⁆ = 0 := by
        intro g
        cases g with
        | inl i =>
          change ⁅⁅T m,T n⁆-((m-n : ℤ) : ℂ) • T (m+n),F (.inl i)⁆ = 0
          rw [defect_bracket,hroot m hm i,hroot n hn i,hroot (m+n) (by omega) i]
          simp
        | inr r =>
          rw [← hnegative r]
          change ⁅⁅T m,T n⁆-((m-n : ℤ) : ℂ) • T (m+n),T (-(r.val : ℤ))⁆ = 0
          rw [defect_bracket]
          simp only [hmixed,lie_add,lie_smul,
            apply_ite,hcentral,smul_zero,lie_zero,ite_self,add_zero,sub_zero]
          have hrpos : (0 : ℤ) < r.val := by exact_mod_cast r.pos
          rw [hsmall m (n-r.val) n hm hn rfl (by omega),
            hsmall n (m-r.val) m hn hm (by omega) (by omega)]
          have hc1 : (m = -(n-(r.val : ℤ))) ↔ (r.val : ℤ) = m+n := by omega
          have hc2 : (n = -(m-(r.val : ℤ))) ↔ (r.val : ℤ) = m+n := by omega
          have hc3 : m+n = (r.val : ℤ) ↔ (r.val : ℤ) = m+n := eq_comm
          have hi1 : m+(n-(r.val : ℤ)) = m+n-r.val := by exact add_sub_assoc' m n (r.val : ℤ)
          have hi2 : n+(m-(r.val : ℤ)) = m+n-r.val := by ring
          simp only [hc1,hc2,hc3,hi1,hi2]
          by_cases heq : (r.val : ℤ) = m+n
          · simp only [if_pos heq]
            rw [heq]
            push_cast
            module
          · simp only [if_neg heq]
            push_cast
            module
      have hD := cyclic_operator_zero F v hspan D hDv hDF
      exact sub_eq_zero.mp hD
  intro m n hm hn
  exact hall (m+n).toNat m n hm hn rfl

theorem full_brackets_from_mixed {A : Type*} [LieRing A] [LieAlgebra ℂ A]
    (T : ℤ → A) (C : A)
    (hmixed : ∀ (m : ℤ) (r : ℕ+), ⁅T m,T (-(r.val : ℤ))⁆ =
      ((m+(r.val : ℤ) : ℤ) : ℂ) • T (m-r.val) +
      if m = r.val then ((m^3-m : ℤ) : ℂ) • C else 0)
    (hzero : ∀ m : ℤ, ⁅T m,T 0⁆ = (m : ℂ) • T m)
    (hpositive : ∀ m n : ℤ, 0 < m → 0 < n →
      ⁅T m,T n⁆ = ((m-n : ℤ) : ℂ) • T (m+n)) :
    ∀ m n : ℤ, ⁅T m,T n⁆ = ((m-n : ℤ) : ℂ) • T (m+n) +
      if m = -n then ((m^3-m : ℤ) : ℂ) • C else 0 := by
  have hneg (m n : ℤ) (hn : n < 0) : ⁅T m,T n⁆ = ((m-n : ℤ) : ℂ) • T (m+n) +
      if m = -n then ((m^3-m : ℤ) : ℂ) • C else 0 := by
    let r : ℕ+ := ⟨(-n).toNat,by omega⟩
    have hr : (r.val : ℤ) = -n := by dsimp [r];rw [Int.toNat_of_nonneg (by omega)]
    have hh := hmixed m r
    simpa [hr,sub_eq_add_neg] using hh
  intro m n
  by_cases hn : n < 0
  · exact hneg m n hn
  · by_cases hn0 : n = 0
    · subst n
      by_cases hm0 : m = 0 <;> simp [hm0,hzero]
    · have hnpos : 0 < n := by omega
      by_cases hm : m < 0
      · rw [← lie_skew,hneg n m hm]
        have hidx : n+m=m+n := by exact Int.add_comm n m
        rw [hidx]
        by_cases heq : m = -n
        · have heq' : n = -m := by exact Int.eq_neg_comm.mp heq
          simp only [if_pos heq,if_pos heq',neg_add,neg_smul]
          rw [heq]
          push_cast
          module
        · have heq' : n ≠ -m := by omega
          simp only [if_neg heq,if_neg heq',add_zero]
          push_cast
          module
      · by_cases hm0 : m = 0
        · subst m
          rw [← lie_skew,hzero]
          simp only [sub_zero,zero_add]
          rw [if_neg (by omega)]
          push_cast
          module
        · rw [hpositive m n (by omega) hnpos,if_neg (by omega),add_zero]


end D5.S3.VertexAlgebra.Sectors.VBKMVirasoroBootstrap
