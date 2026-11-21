/- GID: D5/S3/Quantum/Analysis/RefinedBMVDimThree
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVDimThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined BMV trace-power and exponential lower bounds in dimension three. -/

import D5.S3.Quantum.Analysis.RefinedBMV43
import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate
import D5.S3.Quantum.Analysis.RefinedBMVDimThreePairing

/-! # Three-dimensional refined BMV bounds with three second factors -/

open Matrix NormedSpace
open scoped ComplexOrder BigOperators

noncomputable section

namespace RefinedBMV.DimThree

private abbrev Gap := ℕ × ℕ × ℕ

private def cycle (g : Gap) : Gap := (g.2.1, g.2.2, g.1)
private def swap (g : Gap) : Gap := (g.2.1, g.1, g.2.2)

private theorem gaps_cycle {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) :
    ((gaps p).map cycle).Perm (gaps p) := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem gaps_swap {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) :
    ((gaps p).map swap).Perm (gaps p) := by
  rcases hp with rfl | rfl | rfl <;> decide

private theorem gap_total {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) :
    ((gaps p).all fun g ↦ g.1 + g.2.1 + g.2.2 == p) = true := by
  rcases hp with rfl | rfl | rfl <;> decide

private def monomial {R : Type*} [CommRing R] (a b c : R) (g : Gap) :=
  (a ^ 3) ^ g.1 * (b ^ 3) ^ g.2.1 * (c ^ 3) ^ g.2.2

private theorem defect_cycle {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) (a b c : ℝ) :
    defect p b c a = defect p a b c := by
  unfold defect
  change ((gaps p).map (monomial b c a)).sum - _ = ((gaps p).map (monomial a b c)).sum - _
  have hrot (x y z : ℝ) :
      ((gaps p).map (monomial z x y)).sum = ((gaps p).map (monomial x y z)).sum := by
    have hm : monomial z x y = monomial x y z ∘ cycle := by
      funext g
      simp only [monomial, Function.comp_apply, cycle]
      ring
    rw [hm, ← List.map_map]
    exact ((gaps_cycle hp).map (monomial x y z)).sum_eq
  rw [← hrot b c a]
  ring

private theorem defect_swap {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) (a b c : ℝ) :
    defect p b a c = defect p a b c := by
  unfold defect
  change ((gaps p).map (monomial b a c)).sum - _ = ((gaps p).map (monomial a b c)).sum - _
  have he : monomial b a c = monomial a b c ∘ swap := by
    funext g
    simp only [monomial, Function.comp_apply, swap]
    ring
  rw [he, ← List.map_map, ((gaps_swap hp).map (monomial a b c)).sum_eq]
  ring

private theorem sum_map_const_mul {α : Type*} {R : Type*} [Ring R]
    (l : List α) (f : α → R) (r : R) :
    (l.map fun x ↦ r * f x).sum = r * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, mul_add]

private theorem sum_map_sub_const {α : Type*} {R : Type*} [Ring R]
    (l : List α) (f : α → R) (r : R) :
    (l.map fun x ↦ f x - r).sum = (l.map f).sum - l.length * r := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Nat.cast_add, add_mul]; abel

private theorem sum_map_add {α : Type*} {R : Type*} [AddCommMonoid R]
    (l : List α) (f g : α → R) :
    (l.map fun x ↦ f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc, add_left_comm]

private theorem gap_exponents {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    {g : Gap} (hg : g ∈ gaps p) : g.1 + g.2.1 + g.2.2 = p := by
  exact beq_iff_eq.mp (List.all_eq_true.mp (gap_total hp) g hg)

private theorem defect_diag {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) (a : ℝ) :
    defect p a a a = 0 := by
  unfold defect
  have he : ((gaps p).map (monomial a a a)) = (gaps p).map (fun _ ↦ (a * a * a) ^ p) := by
    apply List.map_congr_left
    intro g hg
    rw [monomial, ← pow_add, ← pow_add, gap_exponents hp hg]
    rw [show a * a * a = a ^ 3 by ring]
  change ((gaps p).map (monomial a a a)).sum - _ = _
  rw [he]
  simp [List.map_const', List.sum_replicate, nsmul_eq_mul]

private theorem defect_nonneg {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ defect p a b c := by
  let m := (a * b * c) ^ p
  let f := monomial a b c
  have hc₁ : ((gaps p).map (fun g ↦ f (cycle g))).sum = ((gaps p).map f).sum := by
    rw [show (fun g ↦ f (cycle g)) = f ∘ cycle by rfl, ← List.map_map]
    exact ((gaps_cycle hp).map f).sum_eq
  have hc₂ : ((gaps p).map (fun g ↦ f (cycle (cycle g)))).sum = ((gaps p).map f).sum := by
    rw [show (fun g ↦ f (cycle (cycle g))) = (fun g ↦ f (cycle g)) ∘ cycle by rfl,
      ← List.map_map, ((gaps_cycle hp).map (fun g ↦ f (cycle g))).sum_eq, hc₁]
  have hsum : 0 ≤ ((gaps p).map fun g ↦ f g + f (cycle g) + f (cycle (cycle g)) -
      3 * m).sum := by
    refine List.sum_nonneg fun x hx ↦ ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    let x := a ^ g.1 * b ^ g.2.1 * c ^ g.2.2
    let y := a ^ g.2.1 * b ^ g.2.2 * c ^ g.1
    let z := a ^ g.2.2 * b ^ g.1 * c ^ g.2.1
    have hxyz : x * y * z = m := by
      dsimp [x, y, z, m]
      rw [mul_pow, mul_pow]
      calc
        _ = a ^ (g.1 + g.2.1 + g.2.2) * b ^ (g.1 + g.2.1 + g.2.2) *
            c ^ (g.1 + g.2.1 + g.2.2) := by simp only [pow_add]; ring
        _ = _ := by rw [gap_exponents hp hg]
    have hcube : f g + f (cycle g) + f (cycle (cycle g)) = x ^ 3 + y ^ 3 + z ^ 3 := by
      simp only [f, monomial, cycle, x, y, z, mul_pow, ← pow_mul, Nat.mul_comm 3]
    rw [hcube, ← hxyz]
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have hz : 0 ≤ z := by dsimp [z]; positivity
    calc
      0 ≤ (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / 2 := by positivity
      _ = _ := by ring
  rw [sum_map_sub_const, sum_map_add, sum_map_add, hc₁, hc₂] at hsum
  change 0 ≤ ((gaps p).map f).sum - _ * m
  nlinarith only [hsum]

private def paired (d : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  Real.sqrt (d b b a * d c c a) + Real.sqrt (d a a b * d c c b) + Real.sqrt (d a a c * d b b c)

private theorem paired_ordered {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcert : 0 ≤ criterion p a b c) :
    defect p a b c ≤ paired (defect p) a b c := by
  have hb := ha.trans hab
  have hc := hb.trans hbc
  let d : ℝ → ℝ → ℝ → ℝ := defect p
  let U := d b b a * d c c a
  let V := d a a b * d c c b
  let W := d a a c * d b b c
  let Q := U + V
  have hn := defect_nonneg hp
  have hU : 0 ≤ U := mul_nonneg (hn _ _ _ hb hb ha) (hn _ _ _ hc hc ha)
  have hV : 0 ≤ V := mul_nonneg (hn _ _ _ ha ha hb) (hn _ _ _ hc hc hb)
  have hW : 0 ≤ W := mul_nonneg (hn _ _ _ ha ha hc) (hn _ _ _ hb hb hc)
  have hQ : 0 ≤ Q := add_nonneg hU hV
  have hroot : Real.sqrt Q ≤ Real.sqrt U + Real.sqrt V := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [Real.sq_sqrt hU, Real.sq_sqrt hV,
      mul_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg V)]
  have hs : (d a b c ^ 2 - Q - W) ^ 2 ≤ (2 * Real.sqrt Q * Real.sqrt W) ^ 2 := by
    change 0 ≤ (↑(4 : ℕ) : ℝ) * Q * W - (d a b c ^ 2 - Q - W) ^ 2 at hcert
    norm_num only [Nat.cast_ofNat] at hcert
    rw [mul_pow, mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hW]
    linarith
  have hs' : d a b c ^ 2 - Q - W ≤ 2 * Real.sqrt Q * Real.sqrt W := by
    have hh := (sq_le_sq₀ (abs_nonneg (d a b c ^ 2 - Q - W))
      (by positivity : 0 ≤ 2 * Real.sqrt Q * Real.sqrt W)).mp (by rwa [sq_abs])
    exact (le_abs_self _).trans hh
  have hsq : d a b c ≤ Real.sqrt Q + Real.sqrt W := by
    apply (sq_le_sq₀ (hn _ _ _ ha hb hc) (by positivity)).mp
    nlinarith [Real.sq_sqrt hQ, Real.sq_sqrt hW]
  exact hsq.trans (add_le_add_left hroot (Real.sqrt W))

private theorem pairing_all {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (hcert : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → 0 ≤ criterion p a b c)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    defect p a b c ≤ paired (defect p) a b c := by
  have hs (x y z : ℝ) : paired (defect p) y x z = paired (defect p) x y z := by
    unfold paired
    rw [mul_comm (defect p y y z) (defect p x x z)]
    abel
  have hr (x y z : ℝ) : paired (defect p) y z x = paired (defect p) x y z := by
    unfold paired
    rw [mul_comm (defect p z z y) (defect p x x y),
      mul_comm (defect p y y z) (defect p x x z)]
    abel
  have ordered (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :=
    paired_ordered hp x y z hx hxy hyz (hcert x y z hx hxy hyz)
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ordered a b c ha hab hbc
    · rcases le_total a c with hac | hca
      · have h := ordered a c b ha hac hcb
        rw [← defect_swap hp a c b, ← hs a c b,
          ← defect_cycle hp c a b, ← hr c a b] at h
        exact h
      · simpa only [defect_cycle hp c a b, hr c a b] using ordered c a b hc hca hab
  · rcases le_total a c with hac | hca
    · simpa only [defect_swap hp a b c, hs a b c] using ordered b a c hb hba hac
    · rcases le_total b c with hbc | hcb
      · simpa only [defect_cycle hp a b c, hr a b c] using ordered b c a hb hbc hca
      · have h := ordered c b a hc hcb hba
        rw [← defect_cycle hp c b a, ← hr c b a, defect_swap hp a b c, hs a b c] at h
        exact h

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

/-- The mean trace of the words with (p) copies of the first factor and three of the second. -/
def mean (p : ℕ) (A B : Mat) : ℂ :=
  ((balancedWords p 3).map (fun w ↦ trace (evalWord A B w))).sum /
    (balancedWords p 3).length

private def rotations (p : ℕ) (g : Gap) : List (List Bool) :=
  (List.range (p + 3)).map (gapWord43 g).rotate

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- The largest enumeration compares two lists of 360 words.
private theorem word_rotations {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) :
    ((balancedWords p 3).flatMap fun w ↦ List.replicate 3 w).Perm
      ((gaps p).flatMap (rotations p)) := by
  rcases hp with rfl | rfl | rfl <;>
    simp only [balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append] <;>
    decide +kernel

private theorem word_counts {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) :
    0 < (balancedWords p 3).length ∧ 0 < (gaps p).length ∧
      3 * (balancedWords p 3).length = (p + 3) * (gaps p).length := by
  rcases hp with rfl | rfl | rfl <;>
    simp only [balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append] <;>
    decide +kernel

private theorem sum_expand {α β : Type*} (l : List α) (f : α → List β) (v : β → ℂ) :
    ((l.flatMap f).map v).sum = (l.map fun a ↦ ((f a).map v).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem mean_eq_gaps {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) (A B : Mat) :
    mean p A B = ((gaps p).map (traceGaps43 A B)).sum / (gaps p).length := by
  let v := fun w ↦ trace (evalWord A B w)
  have hr (g : Gap) : ((rotations p g).map v).sum = (p + 3 : ℂ) * traceGaps43 A B g := by
    simp [rotations, v, Function.comp_def, evalWord_rotate_trace43, evalWord_gap_trace43,
      List.map_const', List.sum_replicate, nsmul_eq_mul]
  have he (w : List Bool) : ((List.replicate 3 w).map v).sum = 3 * v w := by
    simp
    ring
  have h := ((word_rotations hp).map v).sum_eq
  simp only [sum_expand, hr, he, sum_map_const_mul] at h
  obtain ⟨hw, hg, hc⟩ := word_counts hp
  have hcast : 3 * ((balancedWords p 3).length : ℂ) =
      (p + 3 : ℂ) * ((gaps p).length : ℂ) := by exact_mod_cast hc
  change (List.map v (balancedWords p 3)).sum / _ = _
  apply (div_eq_div_iff (by exact_mod_cast hw.ne') (by exact_mod_cast hg.ne')).2
  linear_combination (((gaps p).length : ℂ) / 3) * h -
    ((List.map (traceGaps43 A B) (gaps p)).sum / 3) * hcast

private theorem trace_gap {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (a : Fin 3 → ℝ) (B : Mat) :
    ((gaps p).length : ℂ) *
      (mean p ((diagonal fun i ↦ (a i : ℂ)) ^ 3) B -
        trace (((diagonal fun i ↦ (a i : ℂ)) ^ p * B) ^ 3)) =
      walk B (fun i j k ↦ ((defect p (a i) (a j) (a k) : ℝ) : ℂ)) := by
  let d : Fin 3 → ℂ := fun i ↦ a i
  let f (g : Gap) (i j k : Fin 3) : ℂ := monomial (d i) (d j) (d k) g
  have htrace : traceGaps43 ((diagonal d) ^ 3) B = fun g ↦ walk B (f g) := by
    funext g
    simpa only [traceGaps43, f, monomial, pow_mul, mul_assoc] using
      trace_pow_walk B d (3 * g.1) (3 * g.2.1) (3 * g.2.2)
  have hcube : trace (((diagonal d) ^ p * B) ^ 3) =
      walk B (fun i j k ↦ d i ^ p * d j ^ p * d k ^ p) := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using trace_pow_walk B d p p p
  have hlen : ((gaps p).length : ℂ) ≠ 0 := by exact_mod_cast (word_counts hp).2.1.ne'
  change ((gaps p).length : ℂ) *
    (mean p ((diagonal d) ^ 3) B - trace (((diagonal d) ^ p * B) ^ 3)) = _
  rw [mul_sub, mean_eq_gaps hp, mul_div_cancel₀ _ hlen, htrace, sum_walk43 B, hcube]
  change walk B _ - ((gaps p).length : ℂ) • walk B _ = _
  rw [← map_smul, ← map_sub]
  congr 1
  funext i j k
  change _ = Complex.ofRealHom (defect p (a i) (a j) (a k))
  simp only [defect, map_sub, map_list_sum, map_pow, map_mul, map_natCast, List.map_map,
    Function.comp_def, Complex.ofRealHom_eq_coe, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    f, monomial, d, mul_pow]

private theorem diagonal_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (hcert : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → 0 ≤ criterion p a b c)
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) (B : Mat) (hB : B.PosSemidef) :
    trace (((diagonal fun i ↦ (a i : ℂ)) ^ p * B) ^ 3) ≤
      mean p ((diagonal fun i ↦ (a i : ℂ)) ^ 3) B := by
  have hn := walk_nonneg (defect p) a B hB
    (fun i j k ↦ defect_nonneg hp _ _ _ (ha i) (ha j) (ha k))
    (defect_diag hp) (defect_swap hp) (defect_cycle hp)
    (pairing_all hp hcert _ _ _ (ha 0) (ha 1) (ha 2))
  rw [← trace_gap hp] at hn
  have hlen : (0 : ℝ) < (gaps p).length := by exact_mod_cast (word_counts hp).2.1
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hlen).mp hre),
    (sub_eq_zero.mp (mul_eq_zero.mp him.symm |>.resolve_left hlen.ne')).symm⟩

private theorem mean_map (p : ℕ) (f : Mat ≃ₐ[ℂ] Mat) (hf : ∀ M, trace (f M) = trace M)
    (A B : Mat) : mean p (f A) (f B) = mean p A B := by
  have h (w : List Bool) : evalWord (f A) (f B) w = f (evalWord A B w) := by
    induction w with
    | nil => simp [evalWord]
    | cons b w ih => cases b <;> simp [evalWord, ih]
  simp only [mean, h, hf]

private theorem cubeRoot_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (hcert : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → 0 ≤ criterion p a b c)
    (X B : Mat) (hX : X.PosSemidef) (hB : B.PosSemidef) :
    trace ((X ^ p * B) ^ 3) ≤ mean p (X ^ 3) B := by
  let U := hX.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  have hB' : (f B).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Mat)
  have h := diagonal_bound hp hcert _ hX.eigenvalues_nonneg (f B) hB'
  change trace (((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ p * f B) ^ 3) ≤
    mean p ((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ 3) (f B) at h
  have hd : f X = diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues) :=
    hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  rw [← hd, ← map_pow f, ← map_mul f, ← map_pow f, ← map_pow f, trace_conjugation] at h
  change _ ≤ mean p (f.toAlgEquiv (X ^ 3)) (f.toAlgEquiv B) at h
  simpa only [mean_map p f.toAlgEquiv (trace_conjugation (star U))] using h

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- The trace-power comparison for all PSD complex matrices of size three and (p=5,6,7). -/
theorem product_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (A B : Mat) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ mean p A B := by
  let X := A ^ (1 / 3 : ℝ)
  have hX : 0 ≤ X := CFC.rpow_nonneg
  have hpow (k : ℕ) : X ^ k = A ^ ((1 / 3 : ℝ) * k) := by
    rw [← CFC.rpow_natCast X k hX]
    exact CFC.rpow_rpow_of_exponent_nonneg A (1 / 3) k (by norm_num) (by positivity) hA.nonneg
  have h3 : X ^ (3 : ℕ) = A := by
    rw [hpow, show (1 / 3 : ℝ) * (↑(3 : ℕ) : ℝ) = 1 by norm_num, CFC.rpow_one A hA.nonneg]
  have hp' : X ^ p = A ^ ((p : ℝ) / 3) := by
    rw [hpow]
    congr 1
    ring
  simpa only [h3, hp'] using cubeRoot_bound hp (criterion_nonneg_ordered p hp) X B
    (Matrix.nonneg_iff_posSemidef.mp hX) hB

/-- The refined BMV lower bound for all complex Hermitian size-three inputs and (p=5,6,7). -/
theorem exponential_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ mean p (exp H) (exp K) := by
  let T : Mat := (1 / 3 : ℝ) • H
  let X := exp T
  have hT : T.IsHermitian := hermitian_real_smul hH _
  have hScale : (3 : ℝ) • ((p : ℝ) • T) = (p : ℝ) • H := by
    dsimp only [T]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hpow (k : ℕ) : X ^ k = exp ((k : ℝ) • T) := by
    rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  have h3 : X ^ (3 : ℕ) = exp H := by
    rw [hpow]
    norm_num [T, smul_smul]
  have hE := cubeRoot_bound hp (criterion_nonneg_ordered p hp) X (exp K)
    (exp_posDef hT).posSemidef (exp_posDef hK).posSemidef
  rw [h3, hpow p] at hE
  have hh := hermitian_real_smul hT (p : ℝ)
  have ht := exponential_trace_le_cube ((p : ℝ) • T) K hh hK
  rw [hScale] at ht
  refine le_trans (Complex.le_def.mpr ⟨ht, ?_⟩) hE
  have he : IsSelfAdjoint (trace (exp ((p : ℝ) • H + (3 : ℝ) • K))) := by
    change star (trace _) = _
    rw [← trace_conjTranspose, ((hermitian_real_smul hH p).add (hermitian_real_smul hK 3)).exp.eq]
  rw [(Complex.im_eq_zero_iff_isSelfAdjoint _).mpr he,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
      (trace_cube_isSelfAdjoint _ _ hh.exp hK.exp)]

#print axioms product_bound
#print axioms exponential_bound

end RefinedBMV.DimThree
