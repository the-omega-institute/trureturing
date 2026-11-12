/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportInertiaIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportInertiaIntervals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact interval consumers of the full six-support inertia formula. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportInertia

/-! Source: complete low-spectrum and mixed-inertia sections, revision
b93becea662a746badeadba42fdc3d3eb3db9382, blobs
10576d85188447cea8efba1549722d8e14c050f2 and
ea37044cd1ad3bcff6e1a5a3bf4e91fa8219961d. Counts refer to the actual
six-cell quotient characteristic multiset, including multiplicities. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportInertiaIntervals
open Matrix Polynomial Finset
open D5.S3.Combinatorics.SpectralGraph.SixSupportInertia
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra
open D5.S3.Combinatorics.SpectralGraph.SixSupportIdealIntersectionLift
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

private theorem diagonal_mono (s P x t u : ℝ) (hP : 0 < P) (hx : 0 < x)
    (hxt : x < t) (htu : t ≤ u) :
    s-x-x*P/(t*(t-x)) ≤ s-x-x*P/(u*(u-x)) := by
  have ht : 0 < t := hx.trans hxt
  have hd : t*(t-x) ≤ u*(u-x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htu) (show 0 ≤ u+t-x by linarith)]
  have hf := div_le_div_of_nonneg_left (show 0 ≤ x*P by positivity)
    (show 0 < t*(t-x) by positivity) hd
  linarith

/-- All three source Schur diagonals are ordered on the entire real domain. -/
theorem diagonal_order (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hx : 0 < x) (hxa : x < a) :
    schurDiagonal a b c x 0 ≤ schurDiagonal a b c x 1 ∧
      schurDiagonal a b c x 1 ≤ schurDiagonal a b c x 2 := by
  have hP : 0 < a*b*c := by have := ha.trans_le hab; have := (ha.trans_le hab).trans_le hbc; positivity
  constructor
  · simpa [schurDiagonal, mul_assoc] using
      diagonal_mono (a+b+c) (a*b*c) x a b hP hx hxa hab
  · simpa [schurDiagonal, mul_assoc] using
      diagonal_mono (a+b+c) (a*b*c) x b c hP hx (hxa.trans_le hab) hbc

private theorem lower_positive (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hxa : x < a) (hl : x*b*c < (a-x)*(a+b+c-x)) :
    0 < schurDiagonal a b c x 0 := by
  change 0 < a+b+c-x-x*a*b*c/(a*(a-x))
  have had : 0 < a*(a-x) := by positivity
  apply (sub_pos.mpr ((div_lt_iff₀ had).mpr ?_))
  nlinarith [mul_pos ha (sub_pos.mpr hl)]

private theorem upper_negative (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hxa : x < a) (hu : (c-x)*(a+b+c-x) < x*a*b) :
    schurDiagonal a b c x 2 < 0 := by
  have hc : 0 < c := (ha.trans_le hab).trans_le hbc
  change a+b+c-x-x*a*b*c/(c*(c-x)) < 0
  have hcd : 0 < c*(c-x) := by have := hxa.trans_le (hab.trans hbc); positivity
  apply sub_neg.mpr
  apply (lt_div_iff₀ hcd).mpr
  nlinarith [mul_pos hc (sub_pos.mpr hu)]

private theorem all_positive_counts (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (hx : 0 < x) (hxa : x < a)
    (hk : ∀ i, 0 < schurDiagonal a b c x i) :
    positiveBelow a b c x = 0 ∧ multiplicity a b c x = 0 := by
  classical
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hs : 0 < a+b+c := by positivity
  have hlt (i : Fin 3) : schurDiagonal a b c x i < a+b+c := by
    have hti : 0 < ![a,b,c] i := by fin_cases i <;> assumption
    have htx : x < ![a,b,c] i := by fin_cases i <;> simp <;> linarith
    dsimp [schurDiagonal]
    have hf : 0 < x*a*b*c/(![a,b,c] i*(![a,b,c] i-x)) := by positivity
    linarith
  have h0 := div_lt_div_of_pos_left ha (hk 0) (hlt 0)
  have h1 := div_lt_div_of_pos_left hb (hk 1) (hlt 1)
  have h2 := div_lt_div_of_pos_left hc (hk 2) (hlt 2)
  have he : a/(a+b+c)+b/(a+b+c)+c/(a+b+c) = 1 := by field_simp
  have hF : 1-∑ i : Fin 3, ![a,b,c] i/schurDiagonal a b c x i < 0 := by
    simp only [Fin.sum_univ_three]
    change 1-(a/schurDiagonal a b c x 0+b/schurDiagonal a b c x 1+
      c/schurDiagonal a b c x 2) < 0
    linarith
  have h := schur_nonsingular a b c x ha hab hbc hx hxa (fun i => (hk i).ne')
  have hn : #{i | schurDiagonal a b c x i < 0} = 0 := by
    have hnot (i : Fin 3) : ¬schurDiagonal a b c x i < 0 := not_lt.mpr (hk i).le
    simp only [hnot,Finset.filter_false,Finset.card_empty]
  rw [hn,if_pos hF,if_neg hF.ne] at h
  have hr := positive_root_counts a b c x ha hab hbc hx hxa
  omega

/-- Exact upper-inertia criterion: exactly two positive roots below m,
and no root at m. No endpoint sign-change assumption is used. -/
theorem upper_criterion (a b c m : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hm : 0 < m) (hma : m < a) (hu : (c-m)*(a+b+c-m) < m*a*b) :
    positiveBelow a b c m = 2 ∧ multiplicity a b c m = 0 := by
  classical
  have ho := diagonal_order a b c m ha hab hbc hm hma
  have hc := upper_negative a b c m ha hab hbc hma hu
  have hk (i : Fin 3) : schurDiagonal a b c m i < 0 := by
    fin_cases i
    · exact lt_of_le_of_lt (ho.1.trans ho.2) hc
    · exact lt_of_le_of_lt ho.2 hc
    · exact hc
  have hb : 0 < b := ha.trans_le hab
  have hcpos : 0 < c := hb.trans_le hbc
  have hF : 0 < 1-∑ i : Fin 3, ![a,b,c] i/schurDiagonal a b c m i := by
    have h0 := div_neg_of_pos_of_neg ha (hk 0)
    have h1 := div_neg_of_pos_of_neg hb (hk 1)
    have h2 := div_neg_of_pos_of_neg hcpos (hk 2)
    simp only [Fin.sum_univ_three]
    change 0 < 1-(a/schurDiagonal a b c m 0+b/schurDiagonal a b c m 1+
      c/schurDiagonal a b c m 2)
    linarith
  have h := schur_nonsingular a b c m ha hab hbc hm hma (fun i => (hk i).ne)
  have hn : #{i | schurDiagonal a b c m i < 0} = 3 := by simp [hk]
  rw [hn,if_neg (not_lt.mpr hF.le),if_neg hF.ne'] at h
  have hr := positive_root_counts a b c m ha hab hbc hm hma
  omega

/-- Exact lower-inertia criterion: no positive root at or below x. -/
theorem lower_criterion (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hx : 0 < x) (hxa : x < a) (hl : x*b*c < (a-x)*(a+b+c-x)) :
    positiveBelow a b c x = 0 ∧ multiplicity a b c x = 0 := by
  have ho := diagonal_order a b c x ha hab hbc hx hxa
  have h0 := lower_positive a b c x ha hab hbc hxa hl
  apply all_positive_counts a b c x ha hab hbc hx hxa
  intro i
  fin_cases i
  · exact h0
  · exact h0.trans_le ho.1
  · exact h0.trans_le (ho.1.trans ho.2)

/-- A lower criterion excludes every actual positive quotient root at or
below x, including repeated characteristic roots and the endpoint. -/
theorem root_above_lower (a b c x t : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hx : 0 < x) (hxa : x < a) (hl : x*b*c < (a-x)*(a+b+c-x))
    (ht : 0 < t) (hm : t ∈ (quotient a b c).charpoly.roots) : x < t := by
  classical
  have h := lower_criterion a b c x ha hab hbc hx hxa hl
  by_contra hn
  have htx : t ≤ x := le_of_not_gt hn
  rcases lt_or_eq_of_le htx with htx | rfl
  · exact (Multiset.countP_eq_zero.mp h.1 t hm) ⟨ht,htx⟩
  · exact (Multiset.countP_eq_zero.mp h.2 t hm) rfl


/-- Both low roots lie in the entire original unit interval, counted with
algebraic multiplicities on the actual quotient. -/
theorem unit_interval_count (a b c m : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hm : 2 ≤ m) (hma : m < a)
    (hu : (c-m)*(a+b+c-m) < m*a*b)
    (hl : (m-1)*b*c < (a-m+1)*(a+b+c-m+1)) :
    (quotient a b c).charpoly.roots.countP (fun t => m-1 < t ∧ t < m) = 2 := by
  classical
  have h0 : 0 < m-1 := by linarith
  have hxa : m-1 < a := by linarith
  have hl' : (m-1)*b*c < (a-(m-1))*(a+b+c-(m-1)) := by
    convert hl using 1 <;> ring
  have hu' := (upper_criterion a b c m ha hab hbc (by linarith) hma hu).1
  change (quotient a b c).charpoly.roots.countP (fun t => 0 < t ∧ t < m) = 2 at hu'
  rw [← hu']
  apply Multiset.countP_congr rfl
  intro t ht
  apply propext
  constructor
  · intro h
    exact ⟨h0.trans h.1,h.2⟩
  · intro h
    exact ⟨root_above_lower a b c (m-1) t ha hab hbc h0 hxa hl' h.1 ht,h.2⟩

private theorem root_of_member (a b c t : ℝ) (ht : 0 < t)
    (hm : t ∈ (quotient a b c).charpoly.roots) : h a b c t = 0 := by
  have he := (Polynomial.mem_roots (quotient a b c).charpoly_monic.ne_zero).mp hm
  change (quotient a b c).charpoly.eval t = 0 at he
  rw [Matrix.eval_charpoly,determinant] at he
  exact (mul_eq_zero.mp he).resolve_left ht.ne'

/-- The original two strict inertia inequalities have a real actual-ideal
consumer, with an actual nonzero Laplacian eigenvector supplied by the lift. -/
theorem unit_interval_actual (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c m : ℕ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hm : 2 ≤ m) (hma : m < a)
    (hu : ((c : ℝ)-m)*(a+b+c-m) < (m : ℝ)*a*b)
    (hl : ((m : ℝ)-1)*b*c < (a-m+1)*(a+b+c-m+1)) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  classical
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hcount := unit_interval_count a b c m (by exact_mod_cast ha)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) (by exact_mod_cast hm)
    (by exact_mod_cast hma) hu hl
  obtain ⟨t,ht,hlo,hhi⟩ := Multiset.countP_pos.mp (show 0 <
      (quotient a b c).charpoly.roots.countP (fun t : ℝ => (m : ℝ)-1 < t ∧ t < m) by
    rw [hcount]; norm_num)
  have htpos : 0 < t := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hr := root_of_member a b c t htpos ht
  apply nonintegral_of_unit_root p hp hinj a b c ha hb hc t htpos.ne' hr ((m : ℤ)-1)
  · simpa using hlo
  · push_cast
    linarith

/-- The full balanced real criterion gives an actual quotient eigenvector
strictly between two and three. -/
theorem balanced_interval (a b c : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hl : 2*b*c < (a-2)*(a+b+c-2)) :
    ∃ t : ℝ, 2 < t ∧ t < 3 ∧ ∃ z : Fin 6 → ℝ,
      z ≠ 0 ∧ quotient a b c *ᵥ z = t • z := by
  have ha0 : 0 < a := by linarith
  obtain ⟨t,ht0,ht3,z,hz,he⟩ := positive_real_low_eigenvalue a b c ha0 hab hbc
  have hr := root_of_eigenpair a b c t ht0.ne' z hz he
  have hm : t ∈ (quotient a b c).charpoly.roots := by
    apply (Polynomial.mem_roots (quotient a b c).charpoly_monic.ne_zero).mpr
    change (quotient a b c).charpoly.eval t = 0
    rw [Matrix.eval_charpoly,determinant,hr,mul_zero]
  exact ⟨t,root_above_lower a b c 2 t ha0 hab hbc (by norm_num) (by linarith)
    hl ht0 hm,ht3,z,hz,he⟩

/-- Balanced interval consumed by the actual graph for all distinct primes. -/
theorem balanced_actual (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 4 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hl : 2*(b : ℝ)*c < (a-2)*(a+b+c-2)) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  have ha0 : 0 < a := by omega
  have hb : 0 < b := ha0.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  obtain ⟨t,ht2,ht3,z,hz,he⟩ := balanced_interval a b c (by exact_mod_cast ha)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) hl
  have ht0 : 0 < t := by linarith
  exact nonintegral_of_unit_root p hp hinj a b c ha0 hb hc t ht0.ne'
    (root_of_eigenpair a b c t ht0.ne' z hz he) 2 ht2 (by norm_num; exact ht3)

/-- Exact sharp span threshold for guaranteeing the strict diagonal
criterion; optimality here is only for that sufficient criterion. -/
theorem span_criterion (a d ρ : ℝ) (hρ : 0 ≤ ρ) (hd : 0 ≤ d) (hdρ : d ≤ ρ)
    (ha : ρ+4+Real.sqrt 3*(ρ+2) < a) :
    4 < a ∧ 2*(a+d)*(a+ρ) < (a-2)*(a+(a+d)+(a+ρ)-2) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hbase : 0 < (a-ρ-4-Real.sqrt 3*(ρ+2))*(a-ρ-4+Real.sqrt 3*(ρ+2)) := by
    apply mul_pos <;> nlinarith [mul_pos hs (show 0 < ρ+2 by linarith)]
  have hrest : 0 ≤ (ρ-d)*(a+2*ρ+2) := by
    apply mul_nonneg (sub_nonneg.mpr hdρ)
    nlinarith [mul_pos hs (show 0 < ρ+2 by linarith)]
  constructor
  · nlinarith [mul_pos hs (show 0 < ρ+2 by linarith)]
  · have hf : (a-ρ-4-Real.sqrt 3*(ρ+2))*(a-ρ-4+Real.sqrt 3*(ρ+2)) =
        (a-ρ-4)^2-(Real.sqrt 3*(ρ+2))^2 := by ring
    rw [mul_pow,hs2] at hf
    nlinarith

/-- The older linear span bound implies the sharp sufficient bound. -/
theorem linear_span_implies (a ρ : ℝ) (hρ : 0 ≤ ρ) (ha : 3*ρ+8 ≤ a) :
    ρ+4+Real.sqrt 3*(ρ+2) < a := by
  have hs : Real.sqrt 3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h := mul_pos (sub_pos.mpr hs) (show 0 < ρ+2 by linarith)
  nlinarith

/-- At fixed minimum and span, the criterion is minimized at b=c. -/
theorem span_minimizer (a d ρ : ℝ) (ha : 4 ≤ a) (hdρ : d ≤ ρ) (hρ : 0 ≤ ρ) :
    (a-2)*(a+(a+ρ)+(a+ρ)-2)-2*(a+ρ)*(a+ρ) ≤
      (a-2)*(a+(a+d)+(a+ρ)-2)-2*(a+d)*(a+ρ) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hdρ) (show 0 ≤ a+2*ρ+2 by linarith)]

/-- Exact sharpness for the diagonal sufficient criterion at its minimum.
This asserts no converse about the whole nonintegral spectral region. -/
theorem sharp_span_iff (a ρ : ℝ) (ha : 4 ≤ a) (hρ : 0 ≤ ρ) :
    2*(a+ρ)*(a+ρ) < (a-2)*(a+(a+ρ)+(a+ρ)-2) ↔
      ρ+4+Real.sqrt 3*(ρ+2) < a := by
  have hs : 1 < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < a-ρ-4+Real.sqrt 3*(ρ+2) := by
    nlinarith [mul_pos (sub_pos.mpr hs) (show 0 < ρ+2 by linarith)]
  have hf : (a-ρ-4-Real.sqrt 3*(ρ+2))*(a-ρ-4+Real.sqrt 3*(ρ+2)) =
      (a-ρ-4)^2-(Real.sqrt 3*(ρ+2))^2 := by ring
  rw [mul_pow,hs2] at hf
  constructor
  · intro h
    have hm : 0 < (a-ρ-4-Real.sqrt 3*(ρ+2))*(a-ρ-4+Real.sqrt 3*(ρ+2)) := by nlinarith
    have := (mul_pos_iff_of_pos_right hp).mp hm
    linarith
  · intro h
    have hm := mul_pos (show 0 < a-ρ-4-Real.sqrt 3*(ρ+2) by linarith) hp
    nlinarith


/-- The sharp span condition produces an actual quotient eigenvector in(2,3)
for every real middle position, with unbounded nonnegative span. -/
theorem span_interval (a d ρ : ℝ) (hρ : 0 ≤ ρ) (hd : 0 ≤ d) (hdρ : d ≤ ρ)
    (ha : ρ+4+Real.sqrt 3*(ρ+2) < a) :
    ∃ t : ℝ, 2 < t ∧ t < 3 ∧ ∃ z : Fin 6 → ℝ,
      z ≠ 0 ∧ quotient a (a+d) (a+ρ) *ᵥ z = t • z := by
  have h := span_criterion a d ρ hρ hd hdρ ha
  exact balanced_interval a (a+d) (a+ρ) h.1.le (by linarith) (by linarith) h.2

/-- Every natural-parameter actual graph in the complete sharp-span region
consumes the exact source interval, with no scan or endpoint certificate. -/
theorem span_actual (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a d ρ : ℕ) (hdρ : d ≤ ρ)
    (ha : (ρ : ℝ)+4+Real.sqrt 3*(ρ+2) < a) :
    ¬ActualLaplacianIntegral (modulus p (exponents a (a+d) (a+ρ))) := by
  have h := span_criterion (a : ℝ) d ρ (by positivity) (by positivity)
    (by exact_mod_cast hdρ) ha
  apply balanced_actual p hp hinj a (a+d) (a+ρ) (by exact_mod_cast h.1.le)
    (by omega) (by omega)
  simpa only [Nat.cast_add] using h.2

#print axioms upper_criterion
#print axioms lower_criterion
#print axioms root_above_lower
end D5.S3.Combinatorics.SpectralGraph.SixSupportInertiaIntervals
