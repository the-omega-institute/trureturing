/- GID: D5/S3/Arith/CharacterSums/PascadiShortSlopeDisplacement
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiShortSlopeDisplacement
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Short middle-slope lifts counted by their nonzero displacements. -/

module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Counting lifts of the Pascadi word in a short box of middle-slope coordinates. -/

public section

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

open MvPolynomial

private def displacementPolynomial {K : Type*} [Field K] (v : Fin 3 → K) :
    MvPolynomial (Fin 3) K :=
  C (v 0) * (X 1 * X 2 * (X 1 + X 2)) +
  C (v 1) * (X 0 * X 2 * (X 0 + X 2)) +
  C (v 2) * (X 0 * X 1 * (X 0 + X 1))

private theorem displacementPolynomial_ne_zero {K : Type*} [Field K]
    {v : Fin 3 → K} (hv : v ≠ 0) : displacementPolynomial v ≠ 0 := by
  intro hz
  apply hv
  funext i
  fin_cases i
  · have hc := congrArg (fun f : MvPolynomial (Fin 3) K =>
      (eval₂Hom Polynomial.C (![0, 1, Polynomial.X] : Fin 3 → Polynomial K) f).coeff 1) hz
    simpa [displacementPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_add] using hc
  · have hc := congrArg (fun f : MvPolynomial (Fin 3) K =>
      (eval₂Hom Polynomial.C (![1, 0, Polynomial.X] : Fin 3 → Polynomial K) f).coeff 1) hz
    simpa [displacementPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_add] using hc
  · have hc := congrArg (fun f : MvPolynomial (Fin 3) K =>
      (eval₂Hom Polynomial.C (![1, Polynomial.X, 0] : Fin 3 → Polynomial K) f).coeff 1) hz
    simpa [displacementPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_add] using hc

private theorem displacementPolynomial_degree {K : Type*} [Field K] (v : Fin 3 → K) :
    (displacementPolynomial v).totalDegree ≤ 3 := by
  have h (i j k : Fin 3) :
      (C (v i) * (X j * X k * (X j + X k)) : MvPolynomial (Fin 3) K).totalDegree ≤ 3 := by
    have h₁ : (X j + X k : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := by
      simpa using totalDegree_add (X j : MvPolynomial (Fin 3) K) (X k)
    have h₂ : (X j * X k : MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
      simpa using totalDegree_mul (X j : MvPolynomial (Fin 3) K) (X k)
    have h₃ := totalDegree_mul (X j * X k : MvPolynomial (Fin 3) K) (X j + X k)
    have h₄ := totalDegree_mul (C (v i) : MvPolynomial (Fin 3) K) (X j * X k * (X j + X k))
    rw [totalDegree_C, zero_add] at h₄
    omega
  unfold displacementPolynomial
  exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
    (max_le (h 0 1 2) (h 1 0 2))) (h 2 0 1))

private theorem displacement_zero_count {K : Type*} [Field K] [DecidableEq K]
    (S : Finset K) {v : Fin 3 → K} (hv : v ≠ 0) :
    ((Fintype.piFinset fun _ : Fin 3 => S).filter
      fun b => eval b (displacementPolynomial v) = 0).card ≤ 3 * S.card ^ 2 := by
  by_cases hs : S = ∅
  · simp [hs]
  have hs' : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have h := schwartz_zippel_totalDegree (displacementPolynomial_ne_zero hv) S
  have hsQ : 0 < (S.card : ℚ≥0) := by exact_mod_cast hs'
  have hd := displacementPolynomial_degree v
  have hdQ : ((displacementPolynomial v).totalDegree : ℚ≥0) ≤ 3 := by exact_mod_cast hd
  have h' := h.trans (div_le_div_of_nonneg_right hdQ hsQ.le)
  rw [div_le_div_iff₀ (pow_pos hsQ _) hsQ] at h'
  have h'' : ((Fintype.piFinset fun _ : Fin 3 => S).filter
      fun b => eval b (displacementPolynomial v) = 0).card * S.card ≤ 3 * S.card ^ 3 := by
    exact_mod_cast h'
  exact Nat.le_of_mul_le_mul_right (by simpa [pow_succ, mul_assoc] using h'') hs'

/-- In a grid of residue triples, count one lift per nonempty fibre and
charge each further lift to its nonzero displacement from that lift. -/
private theorem short_slope_displacement_count {K : Type*} [Field K]
    (S : Finset K) (D : Finset (Fin 3 → K))
    (F : (Fin 3 → K) → Finset (Fin 3 → K))
    (hD : ∀ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), ∀ k ∈ F b, ∀ k₀ ∈ F b,
      k ≠ k₀ → k - k₀ ∈ D)
    (hword : ∀ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), ∀ k ∈ F b, ∀ k₀ ∈ F b,
      (k 0 - k₀ 0) * (b 1 * b 2 * (b 1 + b 2)) +
      (k 1 - k₀ 1) * (b 0 * b 2 * (b 0 + b 2)) +
      (k 2 - k₀ 2) * (b 0 * b 1 * (b 0 + b 1)) = 0) :
    ∑ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), (F b).card ≤
      S.card ^ 3 + 3 * D.card * S.card ^ 2 := by
  classical
  let G := Fintype.piFinset (fun _ : Fin 3 => S)
  let D' := D.erase 0
  let Cb (b : Fin 3 → K) := D'.filter (fun v => eval b (displacementPolynomial v) = 0)
  have hb (b) (hbg : b ∈ G) : (F b).card ≤ 1 + (Cb b).card := by
    rcases (F b).eq_empty_or_nonempty with he | ⟨k₀, hk₀⟩
    · simp [he]
    have hbound : ((F b).erase k₀).card ≤ (Cb b).card := by
      apply Finset.card_le_card_of_injOn (fun k => k - k₀)
      · intro k hk
        obtain ⟨hne, hk'⟩ := Finset.mem_erase.mp hk
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hne, hD b hbg k hk' k₀ hk₀ hne⟩, ?_⟩
        simpa [displacementPolynomial] using hword b hbg k hk' k₀ hk₀
      · intro k _ k' _ heq
        exact sub_left_injective heq
    rw [Finset.card_erase_of_mem hk₀] at hbound
    omega
  calc
    _ ≤ ∑ b ∈ G, (1 + (Cb b).card) := Finset.sum_le_sum hb
    _ = G.card + ∑ v ∈ D', (G.filter fun b => eval b (displacementPolynomial v) = 0).card := by
      simp only [Cb, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      apply congrArg (G.card + ·)
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ S.card ^ 3 + 3 * D.card * S.card ^ 2 := by
      have he (v) (hv : v ∈ D') :
          (G.filter fun b => eval b (displacementPolynomial v) = 0).card ≤ 3 * S.card ^ 2 :=
        displacement_zero_count S ((Finset.mem_erase.mp hv).1)
      have ht := Finset.sum_le_sum he
      rw [Finset.sum_const, nsmul_eq_mul] at ht
      have hcard : D'.card ≤ D.card := Finset.card_le_card (Finset.erase_subset _ _)
      have hg : G.card = S.card ^ 3 := by simp [G]
      rw [hg]
      refine Nat.add_le_add_left (ht.trans ?_) _
      exact (Nat.mul_le_mul_right (3 * S.card ^ 2) hcard).trans (le_of_eq (by ac_rfl))

/-- The word evaluated on first coordinates in one middle-slope residue fibre.
The lifted first coordinate is `u * b i + p * e * k i`. -/
def middleSlopeLiftWord (p : ℕ) (d u e : ℤ) (b k : Fin 3 → ℤ) : ℤ :=
  let x (i : Fin 3) := u * b i + (p : ℤ) * e * k i
  x 0 + x 1 + x 2 - d * x 0 * x 1 * x 2

private theorem middleSlopeLiftWord_displacement {p : ℕ} [Fact p.Prime]
    (d u e : ℤ) (b k k₀ : Fin 3 → ℤ) (hu : (u : ZMod p) ≠ 0)
    (he : (e : ZMod p) ≠ 0)
    (hk : (p : ℤ)^2 ∣ middleSlopeLiftWord p d u e b k)
    (hk₀ : (p : ℤ)^2 ∣ middleSlopeLiftWord p d u e b k₀) :
    let B (i : Fin 3) : ZMod p := b i
    let V (i : Fin 3) : ZMod p := k i - k₀ i
    V 0 * (B 1 * B 2 * (B 1 + B 2)) +
    V 1 * (B 0 * B 2 * (B 0 + B 2)) +
    V 2 * (B 0 * B 1 * (B 0 + B 1)) = 0 := by
  let B (i : Fin 3) : ZMod p := b i
  let V (i : Fin 3) : ZMod p := k i - k₀ i
  let H (i : Fin 3) : ℤ := k i - k₀ i
  let L : ℤ := H 0 + H 1 + H 2 - d * u^2 *
    (H 0 * b 1 * b 2 + H 1 * b 0 * b 2 + H 2 * b 0 * b 1)
  let upperTerms (l : Fin 3 → ℤ) := u *
    (l 0 * l 1 * b 2 + l 0 * l 2 * b 1 + l 1 * l 2 * b 0) +
    (p : ℤ) * e * l 0 * l 1 * l 2
  have hdiff : middleSlopeLiftWord p d u e b k - middleSlopeLiftWord p d u e b k₀ =
      (p : ℤ) * e * L - (p : ℤ)^2 * d * e^2 * (upperTerms k - upperTerms k₀) := by
    dsimp [middleSlopeLiftWord, L, H, upperTerms]
    ring
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨z, hz⟩ := dvd_sub hk hk₀
  have hl : (p : ℤ) ∣ e * L := by
    refine ⟨z + d * e^2 * (upperTerms k - upperTerms k₀), ?_⟩
    apply mul_left_cancel₀ hp
    linear_combination hz - hdiff
  have hl' := (ZMod.intCast_zmod_eq_zero_iff_dvd (e * L) p).mpr hl
  have hlin : V 0 + V 1 + V 2 - (d : ZMod p) * (u : ZMod p)^2 *
      (V 0 * B 1 * B 2 + V 1 * B 0 * B 2 + V 2 * B 0 * B 1) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left he
    simpa [L, H, B, V] using hl'
  have hk₀mod : (p : ℤ) ∣ middleSlopeLiftWord p d u e b k₀ := by
    exact dvd_trans ⟨p, by ring⟩ hk₀
  have hword := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (middleSlopeLiftWord p d u e b k₀) p).mpr hk₀mod
  have hword' : (u : ZMod p) * B 0 + (u : ZMod p) * B 1 + (u : ZMod p) * B 2 -
      (d : ZMod p) * ((u : ZMod p) * B 0) * ((u : ZMod p) * B 1) *
        ((u : ZMod p) * B 2) = 0 := by
    simpa [middleSlopeLiftWord, B] using hword
  have hsum : B 0 + B 1 + B 2 - (d : ZMod p) * (u : ZMod p)^2 *
      (B 0 * B 1 * B 2) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hu
    linear_combination hword'
  change V 0 * (B 1 * B 2 * (B 1 + B 2)) +
    V 1 * (B 0 * B 2 * (B 0 + B 2)) + V 2 * (B 0 * B 1 * (B 0 + B 1)) = 0
  linear_combination -(B 0 * B 1 * B 2) * hlin +
    (V 0 * B 1 * B 2 + V 1 * B 0 * B 2 + V 2 * B 0 * B 1) * hsum

/-- Count actual prime-square word lifts from a middle-slope residue box.
The integer representatives of the bases and lifts may depend on the fibre. -/
theorem short_slope_word_count {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (D : Finset (Fin 3 → ZMod p))
    (F : (Fin 3 → ZMod p) → Finset (Fin 3 → ZMod p))
    (base : (Fin 3 → ZMod p) → (Fin 3 → ℤ))
    (lift : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) → (Fin 3 → ℤ))
    (d u e : (Fin 3 → ZMod p) → ℤ)
    (hbase : ∀ b i, (base b i : ZMod p) = b i)
    (hlift : ∀ b k i, (lift b k i : ZMod p) = k i)
    (hu : ∀ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), (u b : ZMod p) ≠ 0)
    (he : ∀ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), (e b : ZMod p) ≠ 0)
    (hword : ∀ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), ∀ k ∈ F b,
      (p : ℤ)^2 ∣ middleSlopeLiftWord p (d b) (u b) (e b) (base b) (lift b k))
    (hD : ∀ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), ∀ k ∈ F b, ∀ k₀ ∈ F b,
      k ≠ k₀ → k - k₀ ∈ D) :
    ∑ b ∈ Fintype.piFinset (fun _ : Fin 3 => S), (F b).card ≤
      S.card ^ 3 + 3 * D.card * S.card ^ 2 := by
  apply short_slope_displacement_count S D F hD
  intro b hb k hk k₀ hk₀
  simpa [hbase, hlift] using middleSlopeLiftWord_displacement (d b) (u b) (e b)
    (base b) (lift b k) (lift b k₀) (hu b hb) (he b hb) (hword b hb k hk)
    (hword b hb k₀ hk₀)

end

end D5.S3.Arith.CharacterSums.Original
