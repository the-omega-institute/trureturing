/- GID: D5/S3/Combinatorics/Circle/TwoSmallPlacement
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoSmallPlacement
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: The even-gap cut and odd-gap seam place both actual SMALL occurrences. -/
module
public import D5.S3.Combinatorics.Circle.TwoSmallProfile

/-! # Explicit placement for two free SMALL gaps -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.TwoSmallPlacement
open SourceWidth

/-- A segment of consecutive physical pairs, checking its intermediate peak
as well as both pair endpoints. -/
private theorem paired_segment (f : ℕ → ℤ) (B : ℤ) (off start len : ℕ)
    (H P : ℕ → ℤ)
    (hH : ∀ j, start ≤ j → j ≤ start + len → 0 ≤ H j ∧ H j ≤ B)
    (hP : ∀ j, start ≤ j → j < start + len → 0 ≤ P j ∧ P j ≤ B)
    (hv : ∀ j, start ≤ j → j < start + len →
      f (off + 2 * j) = P j - H j ∧
      f (off + 2 * j + 1) = H (j + 1) - P j) :
    InStrip f B (H start) (List.range' (off + 2 * start) (2 * len)) ∧
      ((List.range' (off + 2 * start) (2 * len)).map f).sum =
        H (start + len) - H start := by
  induction len generalizing start with
  | zero => simpa [InStrip] using hH start (le_refl _) (by omega)
  | succ len ih =>
    obtain ⟨hp, hn⟩ := hv start (le_refl _) (by omega)
    obtain ⟨ht, hm⟩ := ih (start + 1)
      (fun j hj hjn => hH j (by omega) (by omega))
      (fun j hj hjn => hP j (by omega) (by omega))
      (fun j hj hjn => hv j (by omega) (by omega))
    have he : List.range' (off + 2 * start) (2 * (len + 1)) =
        (off + 2 * start) :: (off + 2 * start + 1) ::
          List.range' (off + 2 * (start + 1)) (2 * len) := by
      rw [show 2 * (len + 1) = (2 * len + 1) + 1 by omega]
      simp only [List.range'_succ]
      congr 2 <;> omega
    rw [he]
    constructor
    · have h0 := hH start (by omega) (by omega)
      have h1 := hP start (by omega) (by omega)
      simp only [InStrip]
      refine ⟨h0.1, h0.2, ?_, ?_, ?_⟩
      · omega
      · omega
      · convert ht using 1 <;> omega
    · simp only [List.map_cons, List.sum_cons]
      rw [hm]
      have he : start + 1 + len = start + (len + 1) := by omega
      rw [he]
      omega

theorem unscale_strip (f : ℕ → ℤ) (C h : ℤ) (word : List ℕ)
    (hs : InStrip (fun i => 3 * f i) (3 * C) (3 * h) word) :
    InStrip f C h word := by
  induction word generalizing h with
  | nil => simp only [InStrip] at *; omega
  | cons x xs ih =>
    refine ⟨by have := hs.1; omega, by have := hs.2.1; omega, ih (h + f x) ?_⟩
    convert hs.2.2 using 1 <;> ring

/-- The cut has no free gate: its two possible algebraic forms are forced
by the difference of the gap lengths. -/
theorem even_cut (p q : ℕ) (hpq : p ≤ q) (hne : 1 ≤ p + q) :
    q - p - 1 < q ∧
      ((p = q ∧ (4 : ℤ) ^ p = (4 : ℤ) ^ q ∧ (4 : ℤ) ^ (q - p - 1) = 1) ∨
       (p < q ∧ (4 : ℤ) ^ q = 4 * (4 : ℤ) ^ p * (4 : ℤ) ^ (q - p - 1))) := by
  refine ⟨by omega, ?_⟩
  by_cases he : p = q
  · subst q; left; simp
  · right
    refine ⟨by omega, ?_⟩
    have hq : q = p + (q - p - 1) + 1 := by omega
    conv_lhs => rw [hq, pow_succ, pow_add]
    ring


private theorem loss_pairs (f : ℕ → ℤ) (B N coeff R : ℤ) (off start len : ℕ)
    (hc : 0 ≤ coeff)
    (hend : 0 ≤ R - coeff * ((4 : ℤ) ^ (start + len) - 1))
    (hpeak : R - coeff * ((4 : ℤ) ^ start - 1) + N -
      coeff * (4 : ℤ) ^ start ≤ B)
    (hpos : coeff * (4 : ℤ) ^ (start + len) ≤ N)
    (hv : ∀ j, start ≤ j → j < start + len →
      f (off + 2 * j) = N - coeff * (4 : ℤ) ^ j ∧
      f (off + 2 * j + 1) = -(N + 2 * coeff * (4 : ℤ) ^ j)) :
    InStrip f B (R - coeff * ((4 : ℤ) ^ start - 1))
      (List.range' (off + 2 * start) (2 * len)) ∧
    ((List.range' (off + 2 * start) (2 * len)).map f).sum =
      -coeff * ((4 : ℤ) ^ (start + len) - (4 : ℤ) ^ start) := by
  let H := fun j => R - coeff * ((4 : ℤ) ^ j - 1)
  let P := fun j => H j + N - coeff * (4 : ℤ) ^ j
  have hb (j : ℕ) (hj : start ≤ j) (he : j ≤ start + len) :
      0 ≤ H j ∧ H j ≤ P j ∧ P j ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hj) hc
    have h2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) he) hc
    dsimp [H, P]
    constructor
    · nlinarith
    constructor <;> nlinarith
  obtain ⟨hs, hm⟩ := paired_segment f B off start len H P
    (fun j hj he => ⟨(hb j hj he).1, le_trans (hb j hj he).2.1 (hb j hj he).2.2⟩)
    (fun j hj he => ⟨le_trans (hb j hj (by omega)).1 (hb j hj (by omega)).2.1,
      (hb j hj (by omega)).2.2⟩) (by
        intro j hj he
        obtain ⟨h1, h2⟩ := hv j hj he
        dsimp [H, P]
        rw [h1, h2, pow_succ]
        constructor <;> ring)
  refine ⟨hs, ?_⟩
  dsimp [H] at hm
  nlinarith only [hm]


private theorem gap_inventory (ell m : ℕ) :
    [0] ++ List.range' 1 ell ++ [ell + 1] ++ List.range' (ell + 2) m =
      List.range (ell + m + 2) := by
  have h1 : List.range' 1 ell ++ [ell + 1] = List.range' 1 (ell + 1) := by
    simpa only [Nat.add_comm] using (List.range'_1_concat (s := 1) (n := ell)).symm
  have h2 : List.range' 1 (ell + 1) ++ List.range' (ell + 2) m =
      List.range' 1 (ell + 1 + m) := by
    simpa only [show 1 + (ell + 1) = ell + 2 by omega] using
      (List.range'_append_1 (s := 1) (m := ell + 1) (n := m))
  calc
    [0] ++ List.range' 1 ell ++ [ell + 1] ++ List.range' (ell + 2) m =
        [0] ++ ((List.range' 1 ell ++ [ell + 1]) ++ List.range' (ell + 2) m) := by
          simp only [List.append_assoc]
    _ = [0] ++ List.range' 1 (ell + 1 + m) := by rw [h1, h2]
    _ = List.range (ell + m + 2) := by
      rw [List.range_eq_range', show ell + m + 2 = (ell + 1 + m) + 1 by omega,
        List.range'_succ]
      rfl


/-- Both SMALL labels are placed separately. The cut is calculated from the
two free even gaps, and all its endpoint and peak gates are consequences. -/
theorem even_placement (p q : ℕ) (hpq : p ≤ q) (hne : 1 ≤ p + q)
    (a b N C : ℤ) (ha : a = (4 : ℤ) ^ p) (hb : b = (4 : ℤ) ^ q)
    (hN : N = 4 * a * b - 1) (hC : C = 2 * a * b - 1)
    (f : ℕ → ℤ) (h0 : f 0 = C - b) (hd : f (2 * p + 1) = C - a)
    (hfirst : ∀ i < p,
      f (2 * i + 1) = N - (2 * b + 1) * (4 : ℤ) ^ i ∧
      f (2 * i + 2) = -(N + 2 * (2 * b + 1) * (4 : ℤ) ^ i))
    (hsecond : ∀ j < q,
      f (2 * p + 2 + 2 * j) = N - (2 * a + 1) * (4 : ℤ) ^ j ∧
      f (2 * p + 3 + 2 * j) = -(N + 2 * (2 * a + 1) * (4 : ℤ) ^ j)) :
    ∃ word : List ℕ, word.Perm (List.range (2 * p + 2 * q + 2)) ∧
      InStrip f (3 * C) 0 word ∧ (word.map f).sum = 0 := by
  let h := q - p - 1
  let v : ℤ := (4 : ℤ) ^ h
  let alpha := 2 * b + 1
  let beta := 2 * a + 1
  let R := C - a
  let T := 2 * b + 1 - beta * v
  have ha1 : 1 ≤ a := by rw [ha]; exact one_le_pow₀ (by norm_num)
  have hb1 : 1 ≤ b := by rw [hb]; exact one_le_pow₀ (by norm_num)
  have hv1 : 1 ≤ v := one_le_pow₀ (by norm_num)
  have haB : a ≤ a * b := by nlinarith [mul_nonneg (by omega : 0 ≤ a) (by omega : 0 ≤ b - 1)]
  have hbA : b ≤ a * b := by nlinarith [mul_nonneg (by omega : 0 ≤ a - 1) (by omega : 0 ≤ b)]
  have hR : 0 ≤ R := by dsimp [R]; nlinarith
  have hN0 : 0 ≤ N := by nlinarith
  have hRC : R + N ≤ 3 * C := by dsimp [R]; nlinarith
  have hca : 0 ≤ alpha := by dsimp [alpha]; omega
  have hcb : 0 ≤ beta := by dsimp [beta]; omega
  obtain ⟨hh, hcut⟩ := even_cut p q hpq hne
  change h < q at hh
  have hT : 0 ≤ T := by
    rcases hcut with ⟨he, heab, hev⟩ | ⟨he, heq⟩
    · have heba : a = b := by rw [ha, hb, he]
      have hv : v = 1 := hev
      dsimp [T, beta]; rw [hv]; nlinarith
    · have heba : b = 4 * a * v := by simpa only [← ha, ← hb] using heq
      have hm := mul_nonneg (by omega : 0 ≤ 6 * a - 1) (by omega : 0 ≤ v)
      dsimp [T, beta]; nlinarith
  have hgate : b + 2 ≤ 2 * beta * v := by
    rcases hcut with ⟨he, heab, hev⟩ | ⟨he, heq⟩
    · have heba : a = b := by rw [ha, hb, he]
      have hv : v = 1 := hev
      dsimp [beta]; rw [hv]; nlinarith
    · have heba : b = 4 * a * v := by simpa only [← ha, ← hb] using heq
      dsimp [beta]; nlinarith
  have hav : v ≤ b := by
    dsimp [v]; rw [hb]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hBpos : beta * b ≤ N := by dsimp [beta]; nlinarith
  have hApos : alpha * a ≤ N := by dsimp [alpha]; nlinarith
  have hmiddle : R - alpha * (a - 1) - beta * (v - 1) = T := by
    dsimp [R, alpha, beta, T]; rw [hC]; ring
  have hmid0 : 0 ≤ R - alpha * (a - 1) := by
    have hm := mul_nonneg hcb (by omega : 0 ≤ v - 1)
    linarith
  have hmidR : R - alpha * (a - 1) ≤ R := by
    have hm := mul_nonneg hca (by omega : 0 ≤ a - 1)
    linarith
  obtain ⟨hsA, hmA⟩ := loss_pairs f (3 * C) N alpha R 1 0 p hca
    (by simpa [ha] using hmid0) (by simpa using (show R + N - alpha ≤ 3 * C by omega))
    (by simpa [ha] using hApos) (by
      intro i _ hi
      constructor
      · simpa only [alpha, show 1 + 2 * i = 2 * i + 1 by omega] using (hfirst i (by omega)).1
      · simpa only [alpha, show 1 + 2 * i + 1 = 2 * i + 2 by omega] using (hfirst i (by omega)).2)
  obtain ⟨hsB, hmB⟩ := loss_pairs f (3 * C) N beta
    (R - alpha * (a - 1)) (2 * p + 2) 0 h hcb
    (by simpa [v, hmiddle] using hT)
    (by simpa using (show R - alpha * (a - 1) + N - beta ≤ 3 * C by omega))
    (by simpa [v] using le_trans (mul_le_mul_of_nonneg_left hav hcb) hBpos) (by
      intro j _ hj
      constructor
      · simpa only [beta] using (hsecond j (by omega)).1
      · simpa only [beta, show 2 * p + 2 + 2 * j + 1 = 2 * p + 3 + 2 * j by omega] using
          (hsecond j (by omega)).2)
  have hafter : T + f 0 = beta * (b - v) := by
    dsimp [T, beta]; rw [h0, hC]; ring
  obtain ⟨hsD, hmD⟩ := loss_pairs f (3 * C) N beta (beta * (b - 1))
    (2 * p + 2) h (q - h) hcb
    (by rw [show h + (q - h) = q by omega, ← hb]; ring_nf; omega)
    (by dsimp [v] at hgate; dsimp [beta] at *; nlinarith)
    (by simpa [show h + (q - h) = q by omega, ← hb] using hBpos) (by
      intro j hj hjq
      constructor
      · simpa only [beta] using (hsecond j (by omega)).1
      · simpa only [beta, show 2 * p + 2 + 2 * j + 1 = 2 * p + 3 + 2 * j by omega] using
          (hsecond j (by omega)).2)
  let A := List.range' 1 (2 * p)
  let B := List.range' (2 * p + 2) (2 * h)
  let D := List.range' (2 * p + 2 + 2 * h) (2 * (q - h))
  let word := [2 * p + 1] ++ A ++ B ++ [0] ++ D
  have hma : (A.map f).sum = -alpha * (a - 1) := by simpa [A, ← ha] using hmA
  have hmb : (B.map f).sum = -beta * (v - 1) := by simpa [B, v] using hmB
  have hmd : (D.map f).sum = -beta * (b - v) := by
    simpa [D, v, show h + (q - h) = q by omega, ← hb] using hmD
  have hsa : InStrip f (3 * C) R A := by simpa [A] using hsA
  have hsb : InStrip f (3 * C) (R - alpha * (a - 1)) B := by simpa [B] using hsB
  have hsd : InStrip f (3 * C) (beta * (b - v)) D := by
    convert hsD using 1 <;> dsimp [D, v] <;> ring
  have hsingle : InStrip f (3 * C) 0 [2 * p + 1] := by
    simp only [InStrip, zero_add]
    rw [hd]
    exact ⟨by omega, by omega, hR, by dsimp [R] at *; omega⟩
  have hsmall : InStrip f (3 * C) T [0] := by
    have he := inStrip_prefix hsd 0
    simp only [List.take_zero, List.map_nil, List.sum_nil, add_zero] at he
    simp only [InStrip]
    exact ⟨hT, by linarith [he.2], by rw [hafter]; exact he.1,
      by rw [hafter]; exact he.2⟩
  have hsAB := inStrip_append hsa (by simpa [hma, sub_eq_add_neg] using hsb)
  have hs0D := inStrip_append hsmall (by simpa only [List.map_singleton,
    List.sum_singleton, hafter] using hsd)
  have hsall := inStrip_append hsingle (by
    simp only [List.map_singleton, List.sum_singleton, zero_add, hd]
    exact inStrip_append hsAB (by
      simp only [List.map_append, List.sum_append, hma, hmb]
      convert hs0D using 1 <;> dsimp [R] at * <;> linarith [hmiddle]))
  have hsword : InStrip f (3 * C) 0 word := by
    simpa only [word, List.append_assoc] using hsall
  have hmword : (word.map f).sum = 0 := by
    simp only [word, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, hma, hmb, hmd, hd]
    dsimp [R] at hmiddle
    linarith [hafter]
  have hBD : B ++ D = List.range' (2 * p + 2) (2 * q) := by
    dsimp [B, D]
    rw [List.range'_append_1]
    congr 1 <;> omega
  have hinventory : [0] ++ A ++ [2 * p + 1] ++ B ++ D =
      List.range (2 * p + 2 * q + 2) := by
    simpa only [A, List.append_assoc, hBD] using gap_inventory (2 * p) (2 * q)
  refine ⟨word, ?_, hsword, hmword⟩
  rw [← hinventory]
  apply List.perm_iff_count.mpr
  intro x
  simp only [word, List.count_append]
  omega



/-- For odd gaps the two SMALL steps occupy a seam. Their intermediate
height is the positive product (2a-1)(2b-1), computed separately. -/
theorem odd_placement (p q : ℕ) (a b N C : ℤ)
    (ha : a = 2 * (4 : ℤ) ^ p) (hb : b = 2 * (4 : ℤ) ^ q)
    (hN : N = 4 * a * b - 1) (hC : C = 2 * a * b - 1)
    (f : ℕ → ℤ) (h0 : f 0 = C + b) (hd : f (2 * p + 2) = -(C + a))
    (hfirstP : ∀ i ≤ p, f (2 * i + 1) = N + (2 * b - 1) * (4 : ℤ) ^ i)
    (hfirstN : ∀ i < p, f (2 * i + 2) = -(N - 2 * (2 * b - 1) * (4 : ℤ) ^ i))
    (hsecondN : ∀ j ≤ q, f (2 * p + 3 + 2 * j) =
      -(N + (2 * a - 1) * (4 : ℤ) ^ j))
    (hsecondP : ∀ j < q, f (2 * p + 4 + 2 * j) =
      N - 2 * (2 * a - 1) * (4 : ℤ) ^ j) :
    ∃ word : List ℕ, word.Perm (List.range (2 * p + 2 * q + 4)) ∧
      InStrip f (3 * C) 0 word ∧ (word.map f).sum = 0 := by
  let D := 2 * b - 1
  let E := 2 * a - 1
  let F := 3 * (C + 1) - (a + 2 * b)
  let H := 3 * (C + 1) - (2 * a + b)
  let X := fun i => D * ((4 : ℤ) ^ i - 1)
  let Y := fun i => N - D + 2 * D * (4 : ℤ) ^ i
  let J := fun j => N + E * b - E * (4 : ℤ) ^ j
  let Z := fun j => E * (b - 2 * (4 : ℤ) ^ j)
  have ha2 : 2 ≤ a := by rw [ha]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 4) (n := p)]
  have hb2 : 2 ≤ b := by rw [hb]; nlinarith [one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 4) (n := q)]
  have hD : 0 ≤ D := by dsimp [D]; omega
  have hE : 0 ≤ E := by dsimp [E]; omega
  have hN0 : 0 ≤ N := by nlinarith [mul_nonneg (by omega : 0 ≤ a - 2) (by omega : 0 ≤ b - 2)]
  have hF : F ≤ 3 * C := by dsimp [F]; omega
  have hH : H ≤ 3 * C := by dsimp [H]; omega
  have hYp : Y p = F := by
    dsimp [Y, D, F]
    rw [hN, hC, ha]
    ring
  have hJ0 : J 0 = H := by
    dsimp [J, E, H]
    rw [hN, hC]
    ring
  have hseam : F + f (2 * p + 2) = E * D := by
    rw [hd]
    dsimp [F, E, D]
    rw [hC]
    ring
  have hseam2 : E * D + f 0 = H := by
    rw [h0]
    dsimp [H, E, D]
    rw [hC]
    ring
  have hED : 0 ≤ E * D := mul_nonneg hE hD
  have hfd : f (2 * p + 2) ≤ 0 := by rw [hd]; nlinarith
  have hf0 : 0 ≤ f 0 := by rw [h0]; nlinarith
  have hF0 : 0 ≤ F := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hXY (i : ℕ) (hi : i ≤ p) : 0 ≤ X i ∧ X i ≤ Y i ∧ Y i ≤ 3 * C := by
    have hpi : 1 ≤ (4 : ℤ) ^ i := one_le_pow₀ (by norm_num)
    have hpow := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hi) hD
    have hp0 : 0 ≤ D * (4 : ℤ) ^ i := mul_nonneg hD (by positivity)
    dsimp [X, Y] at *
    constructor
    · exact mul_nonneg hD (by omega)
    constructor <;> nlinarith
  obtain ⟨hsA, hmA⟩ := paired_segment f (3 * C) 1 0 p X Y
    (fun i _ hi => ⟨(hXY i (by omega)).1,
      le_trans (hXY i (by omega)).2.1 (hXY i (by omega)).2.2⟩)
    (fun i _ hi => ⟨le_trans (hXY i (by omega)).1 (hXY i (by omega)).2.1,
      (hXY i (by omega)).2.2⟩) (by
      intro i _ hi
      have hp := hfirstP i (by omega)
      have hn := hfirstN i (by omega)
      dsimp [X, Y, D]
      rw [show 1 + 2 * i = 2 * i + 1 by omega, show 2 * i + 1 + 1 = 2 * i + 2 by omega,
        hp, hn, pow_succ]
      constructor <;> ring)
  have hlastA : InStrip f (3 * C) (X p) [2 * p + 1] := by
    have hx := hXY p (le_refl _)
    have he : X p + f (2 * p + 1) = F := by
      rw [hfirstP p (le_refl _), ← hYp]
      dsimp [X, Y, D]; ring
    simp only [InStrip]
    exact ⟨hx.1, le_trans hx.2.1 hx.2.2, by rw [he]; exact hF0,
      by rw [he]; exact hF⟩
  let A := List.range' 1 (2 * p + 1)
  have hsa : InStrip f (3 * C) 0 A := by
    have ht := inStrip_append hsA (by simpa [hmA, X] using hlastA)
    simpa [A, X, List.range'_1_concat, Nat.add_comm] using ht
  have hma : (A.map f).sum = F := by
    dsimp [A]
    rw [List.range'_1_concat, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton, hmA, X, pow_zero, sub_self,
      mul_zero, sub_zero, Nat.zero_add]
    rw [show 1 + 2 * p = 2 * p + 1 by omega, hfirstP p (le_refl _), ← hYp]
    dsimp [X, Y, D]; ring
  have hJZ (j : ℕ) (hj : j ≤ q) : 0 ≤ Z j ∧ Z j ≤ J j ∧ J j ≤ 3 * C := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) hj
    have hpow1 : 1 ≤ (4 : ℤ) ^ j := one_le_pow₀ (by norm_num)
    have hpow0 : 0 ≤ E * (4 : ℤ) ^ j := mul_nonneg hE (by positivity)
    have hlo : 0 ≤ b - 2 * (4 : ℤ) ^ j := by rw [hb]; nlinarith
    have hmono := mul_le_mul_of_nonneg_left hpow1 hE
    dsimp [Z, J]
    constructor
    · exact mul_nonneg hE hlo
    constructor <;> nlinarith [hJ0]
  obtain ⟨hsB, hmB⟩ := paired_segment f (3 * C) (2 * p + 3) 0 q J Z
    (fun j _ hj => ⟨le_trans (hJZ j (by omega)).1 (hJZ j (by omega)).2.1,
      (hJZ j (by omega)).2.2⟩)
    (fun j _ hj => ⟨(hJZ j (by omega)).1,
      le_trans (hJZ j (by omega)).2.1 (hJZ j (by omega)).2.2⟩) (by
      intro j _ hj
      have hn := hsecondN j (by omega)
      have hp := hsecondP j (by omega)
      dsimp [J, Z, E]
      rw [hn, show 2 * p + 3 + 2 * j + 1 = 2 * p + 4 + 2 * j by omega,
        hp, pow_succ]
      constructor <;> ring)
  have hlastB : J q + f (2 * p + 3 + 2 * q) = 0 := by
    rw [hsecondN q (le_refl _)]
    dsimp [J, E]
    rw [hb]
    ring
  have hsLastB : InStrip f (3 * C) (J q) [2 * p + 3 + 2 * q] := by
    have hj := hJZ q (le_refl _)
    simp only [InStrip]
    exact ⟨le_trans hj.1 hj.2.1, hj.2.2, by rw [hlastB] <;> omega,
      by rw [hlastB] <;> omega⟩
  let B := List.range' (2 * p + 3) (2 * q + 1)
  have hsb : InStrip f (3 * C) H B := by
    have ht := inStrip_append hsB (by simpa [hmB] using hsLastB)
    simpa [B, hJ0, ← List.range'_1_concat] using ht
  have hmb : (B.map f).sum = -H := by
    dsimp [B]
    rw [List.range'_1_concat, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton, hmB, Nat.zero_add, hJ0]
    linarith
  have hsSmall : InStrip f (3 * C) F [2 * p + 2, 0] := by
    simp only [InStrip]
    exact ⟨hF0, hF, by rw [hseam]; exact hED,
      by linarith, by rw [hseam, hseam2]; exact hH0,
      by rw [hseam, hseam2]; exact hH⟩
  let word := A ++ [2 * p + 2, 0] ++ B
  have hsword : InStrip f (3 * C) 0 word := by
    dsimp only [word]
    rw [List.append_assoc]
    apply inStrip_append hsa
    simp only [zero_add, hma]
    exact inStrip_append hsSmall (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [← add_assoc, hseam, hseam2]
      exact hsb)
  have hmword : (word.map f).sum = 0 := by
    simp only [word, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, hma, hmb]
    linarith
  have hi : [0] ++ A ++ [2 * p + 2] ++ B = List.range (2 * p + 2 * q + 4) := by
    simpa only [A, B, show 2 * p + 1 + 1 = 2 * p + 2 by omega,
      show 2 * p + 1 + 2 = 2 * p + 3 by omega,
      show 2 * p + 1 + (2 * q + 1) + 2 = 2 * p + 2 * q + 4 by omega] using
      gap_inventory (2 * p + 1) (2 * q + 1)
  refine ⟨word, ?_, hsword, hmword⟩
  rw [← hi]
  apply List.perm_iff_count.mpr
  intro x
  simp only [word, List.count_append, List.count_cons, List.count_nil]
  omega


end D5.S3.Combinatorics.Circle.TwoSmallPlacement

