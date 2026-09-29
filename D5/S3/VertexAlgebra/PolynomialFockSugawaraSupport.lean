/- GID: D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockSugawaraSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial support gives an explicit finite interval for each Fock Sugawara sum. -/

/-
proof_shape: normalPair_support_interval: content; L_interval_sum: content
escape_witness: The explicit bound in terms of the largest variable occurring in the input
  polynomial is calculated from the partial derivatives. It is used to construct L and to
  identify every sufficiently wide finite interval with its statewise sum.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport

open MvPolynomial

abbrev Fock := MvPolynomial ℕ ℂ

noncomputable def annihilate (k : ℕ) : Module.End ℂ Fock :=
  (k + 1 : ℂ) • (pderiv k).toLinearMap

noncomputable def create (k : ℕ) : Module.End ℂ Fock :=
  LinearMap.mulLeft ℂ (X k : Fock)

noncomputable def mode : ℤ → Module.End ℂ Fock
  | .ofNat 0 => 0
  | .ofNat (k + 1) => annihilate k
  | .negSucc k => create k

/-- The current is a field because a polynomial contains only finitely many variables. -/
noncomputable def current : VertexOperator ℂ Fock :=
  VertexOperator.of_coeff (fun n => mode (-n - 1)) (by
    intro p
    let B := p.vars.sup id
    refine ⟨-((B : ℤ) + 2), ?_⟩
    intro n hn
    by_contra hle
    have hnlt : n < -((B : ℤ) + 2) := lt_of_not_ge hle
    cases n with
    | ofNat t =>
        simp only [Int.ofNat_eq_natCast] at hnlt
        omega
    | negSucc t =>
        cases t with
        | zero => omega
        | succ k =>
            have hk : B < k := by
              simp only [Int.negSucc_eq] at hnlt
              omega
            have hnot : k ∉ p.vars := by
              intro hmem
              have hbound : k ≤ p.vars.sup id := Finset.le_sup (f := id) hmem
              omega
            have hzero : mode (-(Int.negSucc (k + 1)) - 1) p = 0 := by
              have hi : -(Int.negSucc (k + 1)) - 1 = Int.ofNat (k + 1) := by
                simp [Int.negSucc_eq]
              rw [hi]
              simp [mode, annihilate, pderiv_eq_zero_of_notMem_vars hnot]
            exact hn hzero)

noncomputable def normalPair (i j : ℤ) : Module.End ℂ Fock :=
  if j ≤ i then (mode j).comp (mode i) else (mode i).comp (mode j)

/-- The quadratic normal-ordering summand is supported in an interval determined explicitly
by the variables occurring in the state. -/
theorem normalPair_support_interval (n : ℤ) (p : Fock) :
    Function.support (fun k : ℤ => normalPair (n - k) k p) ⊆
      Set.Ioo (n - (Int.ofNat (p.vars.sup id) + 2))
        (Int.ofNat (p.vars.sup id) + 2) := by
  intro k hk
  let N : ℤ := Int.ofNat (p.vars.sup id) + 2
  have hmode : ∀ j ≥ N, mode j p = 0 := by
    intro j hj
    have hpos : 0 < j := by dsimp [N] at hj; omega
    obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    cases t with
    | zero => omega
    | succ t =>
        have ht : p.vars.sup id < t := by
          dsimp [N] at hj
          omega
        have hnot : t ∉ p.vars := by
          intro hmem
          have hbound : t ≤ p.vars.sup id := Finset.le_sup (f := id) hmem
          omega
        simp [mode, annihilate, pderiv_eq_zero_of_notMem_vars hnot]
  have hsmall : ¬ N ≤ max (n - k) k := by
    intro hlarge
    by_cases h : k ≤ n - k
    · have hi : N ≤ n - k := by omega
      exact hk (by simp [normalPair, h, hmode (n - k) hi])
    · have hj : N ≤ k := by omega
      exact hk (by simp [normalPair, h, hmode k hj])
  simp only [Set.mem_Ioo]
  dsimp [N] at hsmall
  simp only [Int.ofNat_eq_natCast] at hsmall ⊢
  omega

/-- The complex polynomial Fock Sugawara operator is defined by a pointwise finite sum. -/
noncomputable def L (n : ℤ) : Module.End ℂ Fock where
  toFun p := (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (n - k) k p
  map_add' p q := by
    have hp : Function.HasFiniteSupport
        (fun k : ℤ => normalPair (n - k) k p) :=
      (Set.finite_Ioo _ _).subset (normalPair_support_interval n p)
    have hq : Function.HasFiniteSupport
        (fun k : ℤ => normalPair (n - k) k q) :=
      (Set.finite_Ioo _ _).subset (normalPair_support_interval n q)
    simp only [map_add]
    rw [finsum_add_distrib hp hq]
    simp [smul_add]
  map_smul' c p := by
    have hp : Function.HasFiniteSupport
        (fun k : ℤ => normalPair (n - k) k p) :=
      (Set.finite_Ioo _ _).subset (normalPair_support_interval n p)
    simp only [map_smul]
    rw [← smul_finsum' c hp]
    simpa only [RingHom.id_apply] using
      smul_comm (2 : ℂ)⁻¹ c (∑ᶠ k : ℤ, normalPair (n - k) k p)

/-- Every interval containing the explicit support computes the same Sugawara action. -/
theorem L_interval_sum (n : ℤ) (p : Fock) (a b : ℤ)
    (ha : a ≤ n - (Int.ofNat (p.vars.sup id) + 2))
    (hb : Int.ofNat (p.vars.sup id) + 2 ≤ b) :
    L n p = (2 : ℂ)⁻¹ • ∑ k ∈ Finset.Icc a b, normalPair (n - k) k p := by
  change (2 : ℂ)⁻¹ • ∑ᶠ k : ℤ, normalPair (n - k) k p = _
  rw [finsum_eq_sum_of_support_subset]
  intro k hk
  have hinterval := normalPair_support_interval n p hk
  simp only [Set.mem_Ioo] at hinterval
  simpa only [Finset.mem_coe, Finset.mem_Icc] using
    (show a ≤ k ∧ k ≤ b by omega)

end D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
