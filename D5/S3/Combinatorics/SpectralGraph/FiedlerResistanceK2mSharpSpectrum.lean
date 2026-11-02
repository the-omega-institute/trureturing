/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mSharpSpectrum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mSharpSpectrum
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Sharp product equality determines the complete native K2m Laplacian spectrum. -/
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
open FiedlerResistanceK2mOptimizer FiedlerResistanceInvariantWeightsRefutation

/-- Equality in the reciprocal estimate concentrates all excess in one entry. -/
private lemma reciprocal_rigidity {ι : Type*} [Fintype ι] (m : ℕ) (hm : 1 < m)
    (hcard : Fintype.card ι = m+1) (r : ι → ℝ) (t : ℝ) (ht : 0 < t)
    (hr : ∀ i, t ≤ r i) (htrace : (∑ i, r i) = 2*m*t)
    (hinv : t * (∑ i, (r i)⁻¹) = m+1/m) :
    ∃ j, r j = m*t ∧ ∀ i, i ≠ j → r i = t := by
  classical
  let q := fun i => r i/t-1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hq (i : ι) : 0 ≤ q i := by
    dsimp [q]
    rw [sub_nonneg,le_div_iff₀ ht]
    simpa using hr i
  have hsum : (∑ i, q i) = m-1 := by
    simp only [q,Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_const,
      Finset.card_univ,hcard,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_one,htrace]
    field_simp
    <;> ring
  have hqi (i : ι) : q i ≤ m-1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)
  have hd (i : ι) : 0 ≤ q i/(1+q i)-q i/m := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (hq i) (by linarith [hq i]) (by linarith [hqi i])
  have hid (i : ι) : t*(r i)⁻¹ = 1-q i/(1+q i) := by
    have hp : 0 < r i := lt_of_lt_of_le ht (hr i)
    dsimp [q]
    field_simp [ht.ne',hp.ne']
    <;> ring
  have hfrac : (∑ i, q i/(1+q i)) = (m-1)/m := by
    have hh : t*(∑ i,(r i)⁻¹) = (m+1)-∑ i,q i/(1+q i) := by
      rw [Finset.mul_sum]
      simp_rw [hid]
      simp [Finset.sum_sub_distrib,hcard,Nat.cast_add,Nat.cast_one]
    have hn : (m+1 : ℝ)-(m+1/m) = (m-1)/m := by field_simp; ring
    linarith
  have hzero : (∑ i, (q i/(1+q i)-q i/m)) = 0 := by
    rw [Finset.sum_sub_distrib,hfrac,← Finset.sum_div,hsum,sub_self]
  have hterm (i : ι) : q i = 0 ∨ q i = m-1 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd j)).mp hzero i (Finset.mem_univ i)
    have hp : 1+q i ≠ 0 := by linarith [hq i]
    have he : q i*(m-1-q i) = 0 := by
      have heq : q i/(1+q i) = q i/m := sub_eq_zero.mp hi
      field_simp [hp,hm0.ne'] at heq
      nlinarith
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  obtain ⟨j,hj⟩ : ∃ j, q j ≠ 0 := by
    by_contra! h
    have hz : (∑ i,q i) = 0 := by simp [h]
    linarith
  have hjq : q j = m-1 := (hterm j).resolve_left hj
  have hother (i : ι) (hij : i ≠ j) : q i = 0 := by
    have hz : (∑ i ∈ Finset.univ.erase j, q i) = 0 := by
      have hh := Finset.sum_erase_add (Finset.univ) q (Finset.mem_univ j)
      rw [hsum,hjq] at hh
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq k)).mp hz i
      (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩)
  refine ⟨j,?_,?_⟩
  · dsimp [q] at hjq
    have hh := (div_eq_iff ht.ne').mp (show r j/t = m from by linarith)
    exact hh
  · intro i hij
    have hi := hother i hij
    dsimp [q] at hi
    have hh := (div_eq_iff ht.ne').mp (show r i/t = 1 from by linarith)
    simpa using hh

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
