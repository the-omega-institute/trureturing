/- GID: D5/S3/Quantum/Algebra/SplitQuarticIrreducibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/SplitQuarticIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse homogeneous multiaffine quartics cannot factor across a variable cut. -/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-! Homogeneous support and the obstruction to a nontrivial factor variable cut. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.SplitQuarticIrreducibility

open MvPolynomial Finset
open scoped Pointwise
open scoped Classical

variable {k : Type*} [Field k]

/-- The squarefree exponent with exactly the indicated original labels. -/
def squareExponent (I : Finset (Fin 8)) : Fin 8 →₀ ℕ :=
  ∑ i ∈ I, Finsupp.single i 1

lemma square_exponent_apply (I : Finset (Fin 8)) (i : Fin 8) :
    squareExponent I i = if i ∈ I then 1 else 0 := by
  classical
  simp [squareExponent, Finsupp.single_apply]

lemma square_exponent_degree (I : Finset (Fin 8)) :
    (squareExponent I).degree = I.card := by
  classical
  simp [Finsupp.degree_eq_sum, square_exponent_apply]

private lemma coeff_product_disjoint {F G : MvPolynomial (Fin 8) k}
    (hd : Disjoint F.vars G.vars) {a b : Fin 8 →₀ ℕ}
    (ha : a ∈ F.support) (hb : b ∈ G.support) :
    (F * G).coeff (a + b) = F.coeff a * G.coeff b := by
  classical
  apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
  intro u v hu hv huv
  have hzeroF (w : Fin 8 →₀ ℕ) (hw : w ∈ F.support) (i : Fin 8)
      (hi : i ∉ F.vars) : w i = 0 := mem_support_notMem_vars_zero hw hi
  have hzeroG (w : Fin 8 →₀ ℕ) (hw : w ∈ G.support) (i : Fin 8)
      (hi : i ∈ F.vars) : w i = 0 :=
    mem_support_notMem_vars_zero hw (fun hj => Finset.disjoint_left.mp hd hi hj)
  constructor <;> ext i
  · have hi := DFunLike.congr_fun huv i
    by_cases h : i ∈ F.vars
    · simpa [hzeroG v hv i h, hzeroG b hb i h] using hi
    · simp [hzeroF u hu i h, hzeroF a ha i h]
  · have hi := DFunLike.congr_fun huv i
    by_cases h : i ∈ F.vars
    · simp [hzeroG v hv i h, hzeroG b hb i h]
    · simpa [hzeroF u hu i h, hzeroF a ha i h] using hi

private lemma vars_nonempty_of_nonunit {F : MvPolynomial (Fin 8) k}
    (hF : F ≠ 0) (hu : ¬ IsUnit F) : F.vars.Nonempty := by
  classical
  by_contra hn
  have he : F = C (F.coeff 0) := vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hc : F.coeff 0 ≠ 0 := by
    intro h
    apply hF
    simpa [h] using he
  apply hu
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

private lemma cut_count :
    ∀ H : Finset (Fin 8), H.Nonempty → H ≠ univ → ∀ d : Fin 5,
      20 ≤ (((univ : Finset (Fin 8)).powersetCard 4).filter
        (fun I => (I ∩ H).card ≠ d.val)).card := by
  decide +kernel

/-- A homogeneous multiaffine quartic in eight variables with fewer than twenty
zero squarefree quartic coefficients is irreducible over its coefficient field. -/
theorem irreducible_of_fewer_than_twenty_zeros
    (f : MvPolynomial (Fin 8) k)
    (hh : f.IsHomogeneous 4) (hm : ∀ i, f.degreeOf i ≤ 1)
    (hz : (((univ : Finset (Fin 8)).powersetCard 4).filter
      (fun I => f.coeff (squareExponent I) = 0)).card < 20) : Irreducible f := by
  classical
  have hf : f ≠ 0 := by
    intro h
    subst f
    norm_num [Finset.card_powersetCard, Nat.choose] at hz
  have hfu : ¬ IsUnit f := by
    intro hu
    have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have he := hh.totalDegree hf
    omega
  refine ⟨hfu, ?_⟩
  intro F G hFG
  by_contra hn
  obtain ⟨hFu, hGu⟩ := not_or.mp hn
  have hF : F ≠ 0 := left_ne_zero_of_mul (hFG ▸ hf)
  have hG : G ≠ 0 := right_ne_zero_of_mul (hFG ▸ hf)
  have hdis : Disjoint F.vars G.vars := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hFi := mem_vars_iff_degreeOf_ne_zero.mp hi
    have hGi := mem_vars_iff_degreeOf_ne_zero.mp hj
    have hd := hm i
    rw [hFG, degreeOf_mul_eq hF hG] at hd
    omega
  let H := F.vars
  have hH : H.Nonempty := vars_nonempty_of_nonunit hF hFu
  have hHne : H ≠ univ := by
    obtain ⟨j, hj⟩ := vars_nonempty_of_nonunit hG hGu
    intro h
    exact Finset.disjoint_left.mp hdis (by simpa [H, ← h] using mem_univ j) hj
  obtain ⟨a₀, ha₀⟩ := exists_coeff_ne_zero hF
  obtain ⟨b₀, hb₀⟩ := exists_coeff_ne_zero hG
  have hp (a b : Fin 8 →₀ ℕ) (ha : a ∈ F.support) (hb : b ∈ G.support) :
      a.degree + b.degree = 4 := by
    have hc : f.coeff (a + b) ≠ 0 := by
      rw [hFG, coeff_product_disjoint hdis ha hb]
      exact mul_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb)
    have he : (a + b).degree = 4 := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh hc
    simpa only [map_add] using he
  have ha0mem : a₀ ∈ F.support := mem_support_iff.mpr ha₀
  have hb0mem : b₀ ∈ G.support := mem_support_iff.mpr hb₀
  have hd0 := hp a₀ b₀ ha0mem hb0mem
  let d : Fin 5 := ⟨a₀.degree, by omega⟩
  have hcut (I : Finset (Fin 8)) (hc : f.coeff (squareExponent I) ≠ 0) :
      (I ∩ H).card = d.val := by
    have hmem : squareExponent I ∈ (F * G).support := by
      rw [← hFG]
      exact mem_support_iff.mpr hc
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul F G hmem)
    have hadeg : a.degree = a₀.degree := by
      have h1 := hp a b₀ ha hb0mem
      omega
    have hrestrict : ∑ i ∈ H, (squareExponent I) i = a.degree := by
      rw [Finsupp.degree_eq_sum]
      calc
        ∑ i ∈ H, (squareExponent I) i = ∑ i ∈ H, a i := by
          apply sum_congr rfl
          intro i hi
          have hbzero : b i = 0 := mem_support_notMem_vars_zero hb
            (fun hj => Finset.disjoint_left.mp hdis hi hj)
          simpa [← hab, hbzero]
        _ = ∑ i : Fin 8, a i := by
          apply sum_subset (subset_univ H)
          intro i _ hi
          exact mem_support_notMem_vars_zero ha hi
    have hcard : (∑ i ∈ H, (squareExponent I) i) = (I ∩ H).card := by
      simp [square_exponent_apply, Finset.inter_comm]
    exact hcard.symm.trans (hrestrict.trans hadeg)
  have hsub : (((univ : Finset (Fin 8)).powersetCard 4).filter
      (fun I => (I ∩ H).card ≠ d.val)) ⊆
      (((univ : Finset (Fin 8)).powersetCard 4).filter
        (fun I => f.coeff (squareExponent I) = 0)) := by
    intro I hi
    obtain ⟨hi, hc⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨hi, ?_⟩
    by_contra hzI
    exact hc (hcut I hzI)
  exact (not_le_of_gt hz) ((cut_count H hH hHne d).trans (card_le_card hsub))

end D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
