/- GID: D5/S3/Quantum/Magic/ParitySectorMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/ParitySectorMoments
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Qudit parity sectors, Clifford label reduction, clock power sums, and label moments. -/

import D5.S3.Quantum.Magic.SubspaceStabilizerEntropy

/-! # Qudit parity sectors and compressed Weyl fourth moments -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Magic.ParitySectorMoments

open D5.S3.Observer.WindowRegister D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylPhaseArithmetic D5.S3.Quantum.Magic.SubspaceStabilizerEntropy

/-- Qudit parity matrix `P |j⟩ = |-j⟩` on `ℂ^d`. -/
def parityMatrix (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ := (Equiv.neg (ZMod d)).permMatrix ℂ
/-- Even parity sector `E_d = ker(P - I)` in `ℂ^d`. -/
def evenSectorSubspace (d : ℕ) [NeZero d] : Submodule ℂ (ZMod d → ℂ) :=
  LinearMap.ker ((parityMatrix d - 1).mulVecLin)
/-- Odd parity sector `O_d = ker(P + I)` in `ℂ^d`. -/
def oddSectorSubspace (d : ℕ) [NeZero d] : Submodule ℂ (ZMod d → ℂ) :=
  LinearMap.ker ((parityMatrix d + 1).mulVecLin)
/-- Orthogonal projector `(I + P) / 2` onto the even parity sector. -/
def evenProjector (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ := (2 : ℂ)⁻¹ • (1 + parityMatrix d)
/-- Orthogonal projector `(I - P) / 2` onto the odd parity sector. -/
def oddProjector (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ := (2 : ℂ)⁻¹ • (1 - parityMatrix d)
/-- Canonical isometric frame `ℂ^{(d + 1) / 2} → ℂ^d` of the even parity sector (`e_0, e_j^+`). -/
def evenIsometry (d : ℕ) [NeZero d] : Matrix (ZMod d) (Fin ((d + 1) / 2)) ℂ := fun r idx =>
  if idx.val = 0 then (if r = 0 then 1 else 0) else ((Real.sqrt 2 : ℂ))⁻¹ *
    ((if r = (idx.val : ZMod d) then 1 else 0) + (if r = -(idx.val : ZMod d) then 1 else 0))
/-- Canonical isometric frame `ℂ^{(d - 1) / 2} → ℂ^d` of the odd parity sector (`e_{j+1}^-`). -/
def oddIsometry (d : ℕ) [NeZero d] : Matrix (ZMod d) (Fin ((d - 1) / 2)) ℂ := fun r idx =>
  ((Real.sqrt 2 : ℂ))⁻¹ * ((if r = ((idx.val + 1 : ℕ) : ZMod d) then 1 else 0) -
    (if r = -((idx.val + 1 : ℕ) : ZMod d) then 1 else 0))
/-- Diagonal entries `1` and `cos(2 π h j / d)` of the even-sector compression of `Z^h`. -/
def evenClockDiag (d : ℕ) (h : ℤ) : Fin ((d + 1) / 2) → ℝ := fun idx =>
  if idx.val = 0 then 1 else Real.cos (2 * Real.pi * (h : ℝ) * (idx.val : ℝ) / (d : ℝ))
/-- Diagonal entries `cos(2 π h (j + 1) / d)` of the odd-sector compression of `Z^h`. -/
def oddClockDiag (d : ℕ) (h : ℤ) : Fin ((d - 1) / 2) → ℝ := fun idx =>
  Real.cos (2 * Real.pi * (h : ℝ) * ((idx.val + 1 : ℕ) : ℝ) / (d : ℝ))
/-- Power sum `∑_{idx} (evenClockDiag d h idx)^m` of the compressed clock eigenvalues on `E_d`. -/
def evenClockPowerSum (d : ℕ) (h : ℤ) (m : ℕ) : ℝ := ∑ idx, (evenClockDiag d h idx) ^ m
/-- Power sum `∑_{idx} (oddClockDiag d h idx)^m` of the compressed clock eigenvalues on `O_d`. -/
def oddClockPowerSum (d : ℕ) (h : ℤ) (m : ℕ) : ℝ := ∑ idx, (oddClockDiag d h idx) ^ m
/-- Projective Weyl order `d / gcd(a₁, gcd(a₂, d))` of a phase-space label `a ∈ (ZMod d)²`. -/
def weylLabelOrder (d : ℕ) (a : ZMod d × ZMod d) : ℕ := d / Nat.gcd a.1.val (Nat.gcd a.2.val d)

private def zmodFinEquiv (d : ℕ) [NeZero d] : Fin d ≃ ZMod d :=
  ⟨fun i => (i.val : ZMod d), fun x => ⟨x.val, ZMod.val_lt x⟩,
   fun i => by ext; simp [Nat.mod_eq_of_lt i.isLt], ZMod.natCast_zmod_val⟩
private def pairVec {d : ℕ} [NeZero d] (ε : ℂ) (x r : ZMod d) : ℂ :=
  ((Real.sqrt 2 : ℂ))⁻¹ * ((if r = x then 1 else 0) + ε * (if r = -x then 1 else 0))
private def colVec {d : ℕ} [NeZero d] (ε : ℂ) (k : ℕ) (r : ZMod d) : ℂ :=
  if k = 0 then (if r = 0 then 1 else 0) else pairVec ε (k : ZMod d) r
private theorem parityMatrix_apply {d : ℕ} [NeZero d] (i j : ZMod d) :
    parityMatrix d i j = if -i = j then 1 else 0 := by
  simp only [parityMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Equiv.neg_apply]
private theorem parityMatrix_props (d : ℕ) [NeZero d] :
    (parityMatrix d) ^ 2 = 1 ∧ (parityMatrix d)ᴴ = parityMatrix d := by
  refine ⟨by ext i j; rw [sq]; simp only [Matrix.mul_apply, parityMatrix_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul]; rw [Finset.sum_ite_eq Finset.univ (-i)]; simp, ?_⟩
  ext i j; simp only [Matrix.conjTranspose_apply, parityMatrix_apply]
  by_cases h : -j = i <;> [simp [h, show -i = j by rw [← h, neg_neg]];
    simp [h, show -i ≠ j from fun hi => h (by rw [← hi, neg_neg])]]
private theorem zmod_odd_sum_split {d : ℕ} [NeZero d] (hd : Odd d) (f : ZMod d → ℂ) :
    (∑ x : ZMod d, f x) = f 0 + ∑ j ∈ Finset.range ((d - 1) / 2),
      (f ((j + 1 : ℕ) : ZMod d) + f (-((j + 1 : ℕ) : ZMod d))) := by
  rcases hd with ⟨m, hdm⟩; rw [← (zmodFinEquiv d).sum_comp f]
  change (∑ i : Fin d, f (i.val : ZMod d)) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => f (k : ZMod d)) d,
    congrArg Finset.range (by omega : d = (m + 1) + m), Finset.sum_range_add,
    Finset.sum_range_succ']
  have hrefl : (∑ j ∈ Finset.range m, f ((m + 1 + j : ℕ) : ZMod d)) =
      ∑ j ∈ Finset.range m, f (-((j + 1 : ℕ) : ZMod d)) := by
    rw [← Finset.sum_range_reflect (fun j => f ((m + 1 + j : ℕ) : ZMod d)) m]
    refine Finset.sum_congr rfl fun j hj => ?_; have := Finset.mem_range.mp hj
    rw [(by omega : m + 1 + (m - 1 - j) = d - (j + 1))]; congr 1; rw [eq_neg_iff_add_eq_zero,
      ← Nat.cast_add, (by omega : d - (j + 1) + (j + 1) = d), ZMod.natCast_self]
  rw [hrefl, (by omega : (d - 1) / 2 = m), Nat.cast_zero, add_comm _ (f 0), add_assoc,
    ← Finset.sum_add_distrib]
private theorem half_index_disjoint {d : ℕ} [NeZero d] (hd : Odd d)
    {u v : ℕ} (hu1 : 1 ≤ u) (hu2 : u ≤ (d - 1) / 2) (hv1 : 1 ≤ v) (hv2 : v ≤ (d - 1) / 2) :
    (u : ZMod d) ≠ 0 ∧ -(u : ZMod d) ≠ 0 ∧ ((u : ZMod d) = (v : ZMod d) ↔ u = v) ∧
      (u : ZMod d) ≠ -(v : ZMod d) := by
  rcases hd with ⟨m, hdm⟩
  have hvu := (ZMod.val_natCast (n := d) u).trans (Nat.mod_eq_of_lt (by omega))
  have hvv := (ZMod.val_natCast (n := d) v).trans (Nat.mod_eq_of_lt (by omega))
  have hu0 : (u : ZMod d) ≠ 0 := fun h => by have := congrArg ZMod.val h; simp [hvu] at this; omega
  refine ⟨hu0, neg_ne_zero.mpr hu0, ⟨fun h => by simpa [hvu, hvv] using congrArg ZMod.val h,
    fun h => by rw [h]⟩, fun h => Nat.not_dvd_of_pos_of_lt (by omega) (by omega : u + v < d)
      ((ZMod.natCast_eq_zero_iff (u + v) d).mp (by push_cast; exact add_eq_zero_iff_eq_neg.mpr h))⟩
private theorem inv_sqrt2_mul_self : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, (by exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2) :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ))]
private theorem star_inv_sqrt2 : star (((Real.sqrt 2 : ℂ))⁻¹) = ((Real.sqrt 2 : ℂ))⁻¹ := by
  simp [Complex.conj_ofReal]
private theorem star_ite_one_zero (P : Prop) [Decidable P] :
    star (if P then (1 : ℂ) else 0) = if P then 1 else 0 := by split_ifs <;> simp
private theorem pairVec_diag_inner {d : ℕ} [NeZero d] (diag : ZMod d → ℂ)
    (ε : ℂ) (hε_star : star ε = ε) (hε_sq : ε * ε = 1) (x y : ZMod d) :
    (x = y → x ≠ -x → (∑ r : ZMod d, star (pairVec ε x r) * (diag r * pairVec ε y r)) =
      (2 : ℂ)⁻¹ * (diag x + diag (-x))) ∧
    (x ≠ y → x ≠ -y → (∑ r : ZMod d, star (pairVec ε x r) * (diag r * pairVec ε y r)) = 0) := by
  refine ⟨fun hxy hx => ?_, fun hxy hxny => ?_⟩
  · subst hxy; have hterm (r : ZMod d) : star (pairVec ε x r) * (diag r * pairVec ε x r) =
        (2 : ℂ)⁻¹ * ((if r = x then diag x else 0) + (if r = -x then diag (-x) else 0)) := by
      by_cases h1 : r = x
      · subst h1; simp only [pairVec, ↓reduceIte, hx, mul_zero, add_zero, mul_one, star_inv_sqrt2]
        linear_combination diag r * inv_sqrt2_mul_self
      · by_cases h2 : r = -x
        · subst h2; simp only [pairVec, h1, ↓reduceIte, zero_add, mul_one, star_mul,
            star_inv_sqrt2, hε_star]
          linear_combination diag (-x) * ((ε * ε) * inv_sqrt2_mul_self + (2 : ℂ)⁻¹ * hε_sq)
        · simp [pairVec, h1, h2]
    simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib]; simp
  · refine Finset.sum_eq_zero fun r _ => ?_
    have hnx : -x ≠ y := fun h => hxny (by rw [← h, neg_neg])
    have hnxy : -x ≠ -y := fun h => hxy (neg_inj.mp h)
    by_cases h1 : r = x <;> [(subst h1; simp [pairVec, hxy, hxny]);
      (by_cases h2 : r = -x <;> [(subst h2; simp [pairVec, hnx, hnxy]); simp [pairVec, h1, h2]])]
private theorem colVec_diag_inner {d : ℕ} [NeZero d] (hd : Odd d) (diag : ZMod d → ℂ)
    (ε : ℂ) (hε_star : star ε = ε) (hε_sq : ε * ε = 1) {k l : ℕ}
    (hk : k ≤ (d - 1) / 2) (hl : l ≤ (d - 1) / 2) :
    (∑ r : ZMod d, star (colVec ε k r) * (diag r * colVec ε l r)) =
      if k = l then (if k = 0 then diag 0
        else (2 : ℂ)⁻¹ * (diag (k : ZMod d) + diag (-(k : ZMod d)))) else 0 := by
  have hz {u : ℕ} (hu0 : u ≠ 0) (hu : u ≤ (d - 1) / 2) (r : ZMod d) (hr : r = 0) :
      colVec ε u r = 0 := by
    obtain ⟨h1, h2, _⟩ := half_index_disjoint hd (Nat.pos_of_ne_zero hu0) hu
      (Nat.pos_of_ne_zero hu0) hu; simp [colVec, pairVec, hu0, hr, Ne.symm h1, Ne.symm h2]
  by_cases hk0 : k = 0
  · by_cases hl0 : l = 0
    · subst hk0 hl0; simp only [colVec, ↓reduceIte]
      simp_rw [show ∀ r : ZMod d, star (if r = 0 then (1 : ℂ) else 0) *
        (diag r * if r = 0 then 1 else 0) = if r = 0 then diag 0 else 0 from
        fun r => by by_cases hr : r = 0 <;> simp [hr]]; simp
    · simp only [show k ≠ l from fun h => hl0 (h ▸ hk0), ↓reduceIte]
      exact Finset.sum_eq_zero fun r _ => by
        by_cases hr : r = 0 <;> [simp [hz hl0 hl r hr]; simp [colVec, hk0, hr]]
  · by_cases hl0 : l = 0
    · simp only [show k ≠ l from fun h => hk0 (h ▸ hl0), ↓reduceIte]
      exact Finset.sum_eq_zero fun r _ => by
        by_cases hr : r = 0 <;> [simp [hz hk0 hk r hr]; simp [colVec, hl0, hr]]
    · obtain ⟨_, _, heq, hsum⟩ := half_index_disjoint hd (Nat.pos_of_ne_zero hk0) hk
        (Nat.pos_of_ne_zero hl0) hl
      obtain ⟨_, _, _, hsumk⟩ := half_index_disjoint hd (Nat.pos_of_ne_zero hk0) hk
        (Nat.pos_of_ne_zero hk0) hk
      simp only [colVec, hk0, hl0, ↓reduceIte]
      have hp := pairVec_diag_inner diag ε hε_star hε_sq (k : ZMod d) (l : ZMod d)
      by_cases hkl : k = l <;> [(subst hkl; simp only [↓reduceIte]; exact hp.1 rfl hsumk);
        (simp only [hkl, ↓reduceIte]; exact hp.2 (mt heq.mp hkl) hsum)]
private theorem sector_diagonal_compression {d : ℕ} [NeZero d] (hd : Odd d) (diag : ZMod d → ℂ) :
    (evenIsometry d)ᴴ * Matrix.diagonal diag * evenIsometry d =
      Matrix.diagonal (fun idx : Fin ((d + 1) / 2) => if idx.val = 0 then diag 0
        else (2 : ℂ)⁻¹ * (diag (idx.val : ZMod d) + diag (-(idx.val : ZMod d)))) ∧
    (oddIsometry d)ᴴ * Matrix.diagonal diag * oddIsometry d =
      Matrix.diagonal (fun idx : Fin ((d - 1) / 2) => (2 : ℂ)⁻¹ *
        (diag ((idx.val + 1 : ℕ) : ZMod d) + diag (-((idx.val + 1 : ℕ) : ZMod d)))) := by
  have hev (r : ZMod d) (idx : Fin ((d + 1) / 2)) : evenIsometry d r idx = colVec 1 idx.val r := by
    dsimp [evenIsometry, colVec, pairVec]; split_ifs <;> ring
  have hod (r : ZMod d) (idx : Fin ((d - 1) / 2)) :
      oddIsometry d r idx = colVec (-1) (idx.val + 1) r := by
    dsimp [oddIsometry, colVec, pairVec]; ring
  have hleE (idx : Fin ((d + 1) / 2)) : idx.val ≤ (d - 1) / 2 := by
    rcases hd with ⟨m, _⟩; have := idx.isLt; omega
  constructor
  · ext a b; rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_mul]; simp_rw [hev]
    rw [colVec_diag_inner hd diag 1 (star_one ℂ) (mul_one 1) (hleE a) (hleE b)]
    by_cases hab : a = b <;> [(subst hab; simp);
      simp [Matrix.diagonal_apply_ne _ hab, Fin.val_ne_of_ne hab]]
  · ext a b; rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_mul]; simp_rw [hod]
    rw [colVec_diag_inner hd diag (-1) (by simp) (by norm_num)
      (by have := a.isLt; omega) (by have := b.isLt; omega)]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.diagonal_apply_ne _ hab, Fin.val_ne_of_ne hab]
private theorem pairVec_outer_term {d : ℕ} [NeZero d] (ε : ℂ)
    (hε_star : star ε = ε) (hε_sq : ε * ε = 1) (x r s : ZMod d) :
    pairVec ε x r * star (pairVec ε x s) = (2 : ℂ)⁻¹ *
      ((if r = x then 1 else 0) * ((if s = x then 1 else 0) + ε * (if s = -x then 1 else 0)) +
       (if r = -x then 1 else 0) * ((if s = -x then 1 else 0) + ε * (if s = x then 1 else 0))) := by
  unfold pairVec; rw [star_mul, star_inv_sqrt2, star_add, star_mul, hε_star, star_ite_one_zero,
    star_ite_one_zero]; set A : ℂ := if r = x then 1 else 0; set B : ℂ := if r = -x then 1 else 0
  set C : ℂ := if s = x then 1 else 0; set D : ℂ := if s = -x then 1 else 0
  linear_combination (A + ε * B) * (C + ε * D) * inv_sqrt2_mul_self + (2 : ℂ)⁻¹ * B * D * hε_sq
private theorem sector_isometry_and_projectors {d : ℕ} [NeZero d] (hd : Odd d) :
    ((evenIsometry d)ᴴ * evenIsometry d = 1 ∧ (oddIsometry d)ᴴ * oddIsometry d = 1) ∧
    (evenIsometry d * (evenIsometry d)ᴴ = evenProjector d ∧
      oddIsometry d * (oddIsometry d)ᴴ = oddProjector d) := by
  have hiso : (evenIsometry d)ᴴ * evenIsometry d = 1 ∧ (oddIsometry d)ᴴ * oddIsometry d = 1 := by
    have h := sector_diagonal_compression hd (fun _ : ZMod d => (1 : ℂ))
    rw [Matrix.diagonal_one, Matrix.mul_one, Matrix.mul_one] at h
    refine ⟨h.1.trans ?_, h.2.trans ?_⟩ <;>
      (ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply]; split_ifs <;> norm_num)
  let g (ε : ℂ) (r s x : ZMod d) : ℂ :=
    (if r = x then 1 else 0) * ((if s = x then 1 else 0) + ε * (if s = -x then 1 else 0))
  have hpair_sum (ε : ℂ) (hεs : star ε = ε) (hε2 : ε * ε = 1) (r s : ZMod d) :
      (2 : ℂ)⁻¹ * g ε r s 0 + (∑ j ∈ Finset.range ((d - 1) / 2),
        pairVec ε ((j + 1 : ℕ) : ZMod d) r * star (pairVec ε ((j + 1 : ℕ) : ZMod d) s)) =
      (2 : ℂ)⁻¹ * ((1 : Matrix (ZMod d) (ZMod d) ℂ) r s + ε * parityMatrix d r s) := by
    simp_rw [show ∀ j : ℕ, pairVec ε ((j + 1 : ℕ) : ZMod d) r *
        star (pairVec ε ((j + 1 : ℕ) : ZMod d) s) =
      (2 : ℂ)⁻¹ * (g ε r s ((j + 1 : ℕ) : ZMod d) + g ε r s (-((j + 1 : ℕ) : ZMod d))) from
      fun j => by simpa [g, neg_neg] using pairVec_outer_term ε hεs hε2 ((j + 1 : ℕ) : ZMod d) r s,
      ← Finset.mul_sum, ← mul_add, ← zmod_odd_sum_split hd (g ε r s)]
    simp only [g, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Matrix.one_apply, parityMatrix_apply]; congr 1; congr 1
    · by_cases h : s = r <;> [subst h; skip] <;> simp [*, Ne.symm]
    · congr 1; by_cases h : s = -r <;> [subst h; skip] <;> simp [*, Ne.symm]
  refine ⟨hiso, ?_, ?_⟩
  · ext r s; rw [show (evenIsometry d * (evenIsometry d)ᴴ) r s =
        ∑ idx : Fin ((d + 1) / 2), colVec 1 idx.val r * star (colVec 1 idx.val s) by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]; exact Finset.sum_congr rfl
          fun idx _ => by dsimp [evenIsometry, colVec, pairVec]; split_ifs <;> ring,
      Fin.sum_univ_eq_sum_range (fun k => colVec 1 k r * star (colVec 1 k s)) ((d + 1) / 2),
      (by rcases hd with ⟨m, _⟩; omega : (d + 1) / 2 = (d - 1) / 2 + 1), Finset.sum_range_succ',
      add_comm, show colVec 1 0 r * star (colVec 1 0 s) = (2 : ℂ)⁻¹ * g 1 r s 0 by
        by_cases hr : r = 0 <;> by_cases hs : s = 0 <;> norm_num [colVec, g, hr, hs]]
    simpa [colVec, evenProjector] using hpair_sum 1 (star_one ℂ) (mul_one 1) r s
  · ext r s; rw [show (oddIsometry d * (oddIsometry d)ᴴ) r s = ∑ idx : Fin ((d - 1) / 2),
        pairVec (-1) ((idx.val + 1 : ℕ) : ZMod d) r *
          star (pairVec (-1) ((idx.val + 1 : ℕ) : ZMod d) s) by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
        exact Finset.sum_congr rfl fun idx _ => by dsimp [oddIsometry, pairVec]; ring,
      Fin.sum_univ_eq_sum_range (fun k => pairVec (-1) ((k + 1 : ℕ) : ZMod d) r *
        star (pairVec (-1) ((k + 1 : ℕ) : ZMod d) s)) ((d - 1) / 2)]
    have hg0 : g (-1) r s 0 = 0 := by by_cases hr : r = 0 <;> by_cases hs : s = 0 <;> simp [g, *]
    simpa [hg0, oddProjector, sub_eq_add_neg] using hpair_sum (-1) (by simp) (by norm_num) r s
private theorem isometry_range_ker_and_finrank {d n : ℕ} [NeZero d]
    (E : Matrix (ZMod d) (Fin n) ℂ) (P : Matrix (ZMod d) (ZMod d) ℂ) (ε : ℂ) (hEE : Eᴴ * E = 1)
    (hPP : P * P = 1) (hε : ε * ε = 1) (hproj : E * Eᴴ = (2 : ℂ)⁻¹ • (1 + ε • P)) :
    LinearMap.range E.mulVecLin =
      LinearMap.ker ((P - ε • (1 : Matrix (ZMod d) (ZMod d) ℂ)).mulVecLin) ∧
    Module.finrank ℂ (LinearMap.range E.mulVecLin) = n := by
  have hPE : P * (E * Eᴴ) = ε • (E * Eᴴ) := by
    rw [hproj, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hPP]
    ext i j; simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    linear_combination -(2 : ℂ)⁻¹ * P i j * hε
  have hinj : Function.Injective E.mulVecLin := fun u₁ u₂ h => by
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hEE] using congrArg (Eᴴ *ᵥ ·) h
  refine ⟨?_, by rw [← (LinearEquiv.ofInjective _ hinj).finrank_eq]; simp⟩
  ext v; simp only [LinearMap.mem_range, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  refine ⟨?_, fun hv => ⟨Eᴴ *ᵥ v, ?_⟩⟩
  · rintro ⟨u, rfl⟩; rw [← show (E * Eᴴ) *ᵥ (E *ᵥ u) = E *ᵥ u by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hEE], Matrix.mulVec_mulVec, hPE,
      Matrix.smul_mulVec]
  · simp only [Matrix.mulVec_mulVec, hproj, Matrix.smul_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec, hv]; ext i; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (2 : ℂ)⁻¹ * v i * hε

/-- Canonical parity properties, orthonormal sector frames, orthogonal projectors, subspace ranges,
sector dimensions `(d + 1) / 2` and `(d - 1) / 2`, and invariance across isometric embeddings. -/
theorem parity_sectors_bases_and_isometries (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) :
    ((parityMatrix d) ^ 2 = 1 ∧ (parityMatrix d)ᴴ = parityMatrix d) ∧
    ((evenIsometry d)ᴴ * evenIsometry d = 1 ∧ evenIsometry d * (evenIsometry d)ᴴ = evenProjector d ∧
      LinearMap.range (evenIsometry d).mulVecLin = evenSectorSubspace d ∧
      Module.finrank ℂ (evenSectorSubspace d) = (d + 1) / 2) ∧
    ((oddIsometry d)ᴴ * oddIsometry d = 1 ∧ oddIsometry d * (oddIsometry d)ᴴ = oddProjector d ∧
      LinearMap.range (oddIsometry d).mulVecLin = oddSectorSubspace d ∧
      Module.finrank ℂ (oddSectorSubspace d) = (d - 1) / 2) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      (LinearMap.range E.mulVecLin = evenSectorSubspace d →
        E * Eᴴ = evenProjector d ∧ Fintype.card S = (d + 1) / 2 ∧
        (∀ a : ZMod d × ZMod d, labelFourthMoment E a = labelFourthMoment (evenIsometry d) a) ∧
        aseGap E = @aseGap d _ (Fin ((d + 1) / 2)) _ ⟨by rw [Fintype.card_fin]; omega⟩
          (evenIsometry d)) ∧
      (LinearMap.range E.mulVecLin = oddSectorSubspace d →
        E * Eᴴ = oddProjector d ∧ Fintype.card S = (d - 1) / 2 ∧
        (∀ a : ZMod d × ZMod d, labelFourthMoment E a = labelFourthMoment (oddIsometry d) a) ∧
        aseGap E = @aseGap d _ (Fin ((d - 1) / 2)) _ ⟨by rw [Fintype.card_fin]; omega⟩
          (oddIsometry d))) := by
  obtain ⟨⟨hEE, hOO⟩, hprojE, hprojO⟩ := sector_isometry_and_projectors hd
  have hPP : parityMatrix d * parityMatrix d = 1 := by simpa [sq] using (parityMatrix_props d).1
  have hkerE := isometry_range_ker_and_finrank (evenIsometry d) (parityMatrix d) 1 hEE hPP
    (mul_one 1) (by simpa [evenProjector] using hprojE)
  have hkerO := isometry_range_ker_and_finrank (oddIsometry d) (parityMatrix d) (-1) hOO hPP
    (by norm_num) (by simpa [oddProjector, sub_eq_add_neg] using hprojO)
  have hrangeE : LinearMap.range (evenIsometry d).mulVecLin = evenSectorSubspace d :=
    by simpa [evenSectorSubspace] using hkerE.1
  have hrangeO : LinearMap.range (oddIsometry d).mulVecLin = oddSectorSubspace d :=
    by simpa [oddSectorSubspace, sub_eq_add_neg] using hkerO.1
  refine ⟨parityMatrix_props d, ⟨hEE, hprojE, hrangeE, hrangeE ▸ hkerE.2⟩,
    ⟨hOO, hprojO, hrangeO, hrangeO ▸ hkerO.2⟩, fun {S} _ _ _ E hE => ?_⟩
  have : NeZero (Fintype.card (Fin ((d + 1) / 2))) := ⟨by rw [Fintype.card_fin]; omega⟩
  have : NeZero (Fintype.card (Fin ((d - 1) / 2))) := ⟨by rw [Fintype.card_fin]; omega⟩
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have h := (subspace_gap_isometry_invariance_and_twirl d).1 E (evenIsometry d) hE hEE
    obtain ⟨hcard, hmom, _, hgap⟩ := h.2 (hr.trans hrangeE.symm)
    exact ⟨(h.1.mp (hr.trans hrangeE.symm)).trans hprojE, by simpa using hcard, hmom, hgap⟩
  · have h := (subspace_gap_isometry_invariance_and_twirl d).1 E (oddIsometry d) hE hOO
    obtain ⟨hcard, hmom, _, hgap⟩ := h.2 (hr.trans hrangeO.symm)
    exact ⟨(h.1.mp (hr.trans hrangeO.symm)).trans hprojO, by simpa using hcard, hmom, hgap⟩
private theorem windowRoot_pow_mod_nat {d : ℕ} [NeZero d] (n : ℕ) :
    windowRoot d ^ (n % d) = windowRoot d ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n d]
  rw [pow_add, pow_mul, (windowRoot_isPrimitiveRoot d).pow_eq_one, one_pow, one_mul]
private theorem windowRoot_pow_unit {d : ℕ} [NeZero d] (n : ℕ) :
    windowRoot d ^ n * star (windowRoot d ^ n) = 1 := by
  have hN : ‖windowRoot d ^ n‖ = 1 := by
    rw [norm_pow, (windowRoot_isPrimitiveRoot d).norm'_eq_one (NeZero.ne d), one_pow]
  rw [mul_comm]; simpa [RCLike.star_def, hN] using RCLike.conj_mul (windowRoot d ^ n)
private theorem windowRoot_star_pow_val {d : ℕ} [NeZero d] (u : ZMod d) :
    star (windowRoot d ^ u.val) = windowRoot d ^ (-u).val :=
  mul_left_cancel₀ (pow_ne_zero u.val ((windowRoot_isPrimitiveRoot d).ne_zero (NeZero.ne d)))
    ((windowRoot_pow_unit u.val).trans
      (by rw [← windowRoot_pow_val_add, add_neg_cancel, ZMod.val_zero, pow_zero]))
private theorem windowRoot_char_sum {d : ℕ} [NeZero d] (a : ZMod d) :
    (∑ j : ZMod d, windowRoot d ^ (a * j).val) = if a = 0 then (d : ℂ) else 0 := by
  simp_rw [show ∀ j : ZMod d, windowRoot d ^ (a * j).val = (windowRoot d ^ a.val) ^ j.val from
      fun j => by rw [ZMod.val_mul, windowRoot_pow_mod_nat, pow_mul],
    ← (zmodFinEquiv d).sum_comp (fun j : ZMod d => (windowRoot d ^ a.val) ^ j.val)]
  change (∑ i : Fin d, (windowRoot d ^ a.val) ^ ((i.val : ZMod d).val)) = _
  simp_rw [show ∀ i : Fin d, ((i.val : ZMod d).val) = i.val from
    fun i => (ZMod.val_natCast (n := d) i.val).trans (Nat.mod_eq_of_lt i.isLt)]
  rw [Fin.sum_univ_eq_sum_range (fun k => (windowRoot d ^ a.val) ^ k) d]; by_cases ha : a = 0
  · subst ha; simp
  · simp only [ha, ↓reduceIte]; have hgeom := geom_sum_mul (windowRoot d ^ a.val) d
    rw [← pow_mul, mul_comm a.val d, pow_mul, (windowRoot_isPrimitiveRoot d).pow_eq_one,
      one_pow, sub_self] at hgeom; exact (mul_eq_zero.mp hgeom).resolve_right fun h =>
      Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero fun hv => ha ((ZMod.val_eq_zero a).mp hv))
        (ZMod.val_lt a) (((windowRoot_isPrimitiveRoot d).pow_eq_one_iff_dvd a.val).mp
          (sub_eq_zero.mp h))
private def dftMatrix (d : ℕ) [NeZero d] : Matrix (ZMod d) (ZMod d) ℂ :=
  fun l j => ((Real.sqrt d : ℂ))⁻¹ * windowRoot d ^ (l * j).val
private def quadPhaseMatrix (d : ℕ) [NeZero d] : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal (fun j : ZMod d => windowRoot d ^ ((((d + 1) / 2 : ℕ) : ZMod d) * j * j).val)
private theorem unit_mul {a b : ℂ} (ha : a * star a = 1) (hb : b * star b = 1) :
    (a * b) * star (a * b) = 1 := by
  calc (a * b) * star (a * b) = (a * star a) * (b * star b) := by simp [star_mul']; ring
    _ = 1 := by rw [ha, hb, mul_one]
private theorem tau_pow_unit (d n : ℕ) : tau d ^ n * star (tau d ^ n) = 1 := by
  have h1 : tau d * star (tau d) = 1 := by
    unfold tau; rw [star_neg, neg_mul_neg]
    change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]; simp [neg_div]
  rw [star_pow, ← mul_pow, h1, one_pow]
private theorem paper_from_disp {d : ℕ} [NeZero d] (U : Matrix (ZMod d) (ZMod d) ℂ)
    (hUU : U * Uᴴ = 1) (a b : ZMod d × ZMod d) (c0 : ℂ) (hc0 : c0 * star c0 = 1)
    (hcomm : U * displacement d a.1 a.2 = c0 • (displacement d b.1 b.2 * U)) :
    ∃ c : ℂ, c * star c = 1 ∧ U * paperDisplacement d a * Uᴴ = c • paperDisplacement d b := by
  have hdisp : U * displacement d a.1 a.2 * Uᴴ = c0 • displacement d b.1 b.2 := by
    rw [hcomm, Matrix.smul_mul, Matrix.mul_assoc, hUU, Matrix.mul_one]
  refine ⟨tau d ^ (a.1.val * a.2.val) * c0 * star (tau d ^ (b.1.val * b.2.val)),
    unit_mul (unit_mul (tau_pow_unit d _) hc0)
      (by rw [star_star, mul_comm]; exact tau_pow_unit d _), ?_⟩
  unfold paperDisplacement; rw [Matrix.mul_smul, Matrix.smul_mul, hdisp, smul_smul, smul_smul]
  congr 1
  calc tau d ^ (a.1.val * a.2.val) * c0 = tau d ^ (a.1.val * a.2.val) * c0 *
        (tau d ^ (b.1.val * b.2.val) * star (tau d ^ (b.1.val * b.2.val))) := by
          rw [tau_pow_unit, mul_one]
    _ = _ := by ring
private theorem disp_apply {d : ℕ} [NeZero d] (a b i j : ZMod d) :
    displacement d a b i j = if i - j = a then windowRoot d ^ (b * j).val else 0 := by
  have hsh (n : ℕ) (r s : ZMod d) :
      (shiftMatrix d ^ n) r s = if r - s = (n : ZMod d) then 1 else 0 := by
    induction n generalizing r s with | zero => simp [Matrix.one_apply, sub_eq_zero] | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]; simp_rw [ih, shiftMatrix, Matrix.circulant_apply,
        mul_ite, mul_one, mul_zero, show ∀ k : ZMod d, (k - s = 1) ↔ (k = s + 1) from
          fun k => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩]
      rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      exact if_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩ rfl rfl
  unfold displacement clockMatrix
  rw [Matrix.diagonal_pow, Matrix.mul_diagonal, hsh, ZMod.natCast_zmod_val, Pi.pow_apply, ite_mul,
    one_mul, zero_mul, ← pow_mul, ← windowRoot_pow_mod_nat, mul_comm j.val b.val, ← ZMod.val_mul]
private theorem dft_and_quadPhase_action {d : ℕ} [NeZero d] (hd : Odd d) :
    ((dftMatrix d)ᴴ * dftMatrix d = 1 ∧
      dftMatrix d * parityMatrix d = parityMatrix d * dftMatrix d ∧
      ∀ x y : ZMod d, ∃ c : ℂ, c * star c = 1 ∧ dftMatrix d * paperDisplacement d (x, y) *
        (dftMatrix d)ᴴ = c • paperDisplacement d (-y, x)) ∧
    ((quadPhaseMatrix d)ᴴ * quadPhaseMatrix d = 1 ∧
      quadPhaseMatrix d * parityMatrix d = parityMatrix d * quadPhaseMatrix d ∧
      ∀ x y : ZMod d, ∃ c : ℂ, c * star c = 1 ∧
        quadPhaseMatrix d * paperDisplacement d (x, y) * (quadPhaseMatrix d)ᴴ =
          c • paperDisplacement d (x, x + y)) := by
  have hd_ne : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hsqrt_inv : ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ = (d : ℂ)⁻¹ := by
    rw [← mul_inv, (by exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d) :
      (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ))]
  have hsr : star (((Real.sqrt d : ℂ))⁻¹) = ((Real.sqrt d : ℂ))⁻¹ := by simp [Complex.conj_ofReal]
  have hF_unit : (dftMatrix d)ᴴ * dftMatrix d = 1 := by
    ext i j; simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dftMatrix, Matrix.one_apply]
    simp_rw [show ∀ l : ZMod d, star (((Real.sqrt d : ℂ))⁻¹ * windowRoot d ^ (l * i).val) *
        (((Real.sqrt d : ℂ))⁻¹ * windowRoot d ^ (l * j).val) =
        (d : ℂ)⁻¹ * windowRoot d ^ ((j - i) * l).val from fun l => by
      rw [star_mul', hsr, windowRoot_star_pow_val]
      calc _ = (((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹) *
                (windowRoot d ^ (-(l * i)).val * windowRoot d ^ (l * j).val) := by ring
        _ = _ := by
              rw [hsqrt_inv, ← windowRoot_pow_val_add, (by ring : -(l * i) + l * j = (j - i) * l)],
      ← Finset.mul_sum]; rw [windowRoot_char_sum]
    by_cases hij : i = j <;> [(subst hij; simp [hd_ne]); simp [hij, sub_ne_zero.mpr (Ne.symm hij)]]
  have hF_par : dftMatrix d * parityMatrix d = parityMatrix d * dftMatrix d := by
    ext l j; simp only [Matrix.mul_apply, parityMatrix_apply, mul_ite, ite_mul, mul_one, mul_zero,
      one_mul, zero_mul]; simp_rw [show ∀ k : ZMod d, (-k = j) ↔ (k = -j) from
      fun k => ⟨fun h => by rw [← h, neg_neg], fun h => by rw [h, neg_neg]⟩]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte, dftMatrix, (by ring : l * -j = -l * j)]
  have hS_unit : (quadPhaseMatrix d)ᴴ * quadPhaseMatrix d = 1 := by
    unfold quadPhaseMatrix; rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j; simp only [Matrix.diagonal_apply, Matrix.one_apply, Pi.star_apply]; by_cases h : i = j
    · subst h; simp only [↓reduceIte]; rw [mul_comm]; exact windowRoot_pow_unit _
    · simp [h]
  have hS_par : quadPhaseMatrix d * parityMatrix d = parityMatrix d * quadPhaseMatrix d := by
    ext i j; simp only [quadPhaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      parityMatrix_apply]; by_cases h : -i = j <;> [subst h; skip] <;> simp [*]
  let mZ : ZMod d := (((d + 1) / 2 : ℕ) : ZMod d); have hmZ2 : mZ + mZ = 1 := by
    rcases hd with ⟨m, _⟩; rw [show mZ + mZ = ((d + 1 : ℕ) : ZMod d) by
      dsimp [mZ]; rw [← Nat.cast_add, (by omega : (d + 1) / 2 + (d + 1) / 2 = d + 1)]]
    push_cast; simp
  refine ⟨⟨hF_unit, hF_par, fun x y => paper_from_disp _ (mul_eq_one_comm.mp hF_unit) (x, y)
    (-y, x) (windowRoot d ^ (-(x * y)).val) (windowRoot_pow_unit _) ?_⟩,
    ⟨hS_unit, hS_par, fun x y => paper_from_disp _ (mul_eq_one_comm.mp hS_unit) (x, y) (x, x + y)
      (windowRoot d ^ (mZ * x * x).val) (windowRoot_pow_unit _) ?_⟩⟩
  · ext l j; simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, dftMatrix, disp_apply,
      mul_ite, ite_mul, mul_zero, zero_mul]
    simp_rw [show ∀ k : ZMod d, (k - j = x) ↔ (k = j + x) from
        fun k => ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩,
      show ∀ k : ZMod d, (l - k = -y) ↔ (k = l + y) from
        fun k => ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']; simp only [Finset.mem_univ, ↓reduceIte]
    calc ((Real.sqrt d : ℂ))⁻¹ * windowRoot d ^ (l * (j + x)).val * windowRoot d ^ (y * j).val
        = ((Real.sqrt d : ℂ))⁻¹ * windowRoot d ^ (l * (j + x) + y * j).val := by
            rw [mul_assoc, ← windowRoot_pow_val_add]
      _ = windowRoot d ^ (-(x * y)).val * (windowRoot d ^ (x * (l + y)).val *
            (((Real.sqrt d : ℂ))⁻¹ * windowRoot d ^ ((l + y) * j).val)) := by
            rw [(by ring : l * (j + x) + y * j = -(x * y) + (x * (l + y) + (l + y) * j)),
              windowRoot_pow_val_add, windowRoot_pow_val_add]; ring
  · ext i j; simp only [quadPhaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, disp_apply]; by_cases h : i - j = x
    · have hi : i = j + x := by linear_combination h
      subst hi; simp only [add_sub_cancel_left, ↓reduceIte]
      change windowRoot d ^ (mZ * (j + x) * (j + x)).val * _ = _
      rw [← windowRoot_pow_val_add, show mZ * (j + x) * (j + x) + y * j =
          mZ * x * x + ((x + y) * j + mZ * j * j) by
        calc mZ * (j + x) * (j + x) + y * j
            = mZ * x * x + ((mZ + mZ) * x * j + y * j + mZ * j * j) := by ring
          _ = _ := by rw [hmZ2]; ring, windowRoot_pow_val_add, windowRoot_pow_val_add]
    · simp [h]

/-- Origin normalization and parity-commuting Clifford reduction of every nonzero Weyl label to a
pure clock label `(0, h)` preserving `gcd(·, d)` on both the even and odd parity sectors. -/
theorem parity_clifford_label_reduction (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) :
    (labelFourthMoment (evenIsometry d) (0, 0) = 1 ∧ labelFourthMoment (oddIsometry d) (0, 0) = 1) ∧
    (∀ a : ZMod d × ZMod d, a ≠ (0, 0) → ∃ h : ℤ,
      Int.gcd h d = Int.gcd (a.1.val : ℤ) (Int.gcd (a.2.val : ℤ) d) ∧
      labelFourthMoment (evenIsometry d) a = labelFourthMoment (evenIsometry d) (0, (h : ZMod d)) ∧
      labelFourthMoment (oddIsometry d) a =
        labelFourthMoment (oddIsometry d) (0, (h : ZMod d))) := by
  have : NeZero (Fintype.card (Fin ((d + 1) / 2))) := ⟨by rw [Fintype.card_fin]; omega⟩
  have : NeZero (Fintype.card (Fin ((d - 1) / 2))) := ⟨by rw [Fintype.card_fin]; omega⟩
  obtain ⟨⟨hEE, hOO⟩, hprojE, hprojO⟩ := sector_isometry_and_projectors hd
  obtain ⟨⟨hF_u, hF_p, hF_a⟩, ⟨hS_u, hS_p, hS_a⟩⟩ := dft_and_quadPhase_action hd
  have hinvE := (subspace_gap_isometry_invariance_and_twirl d).2.1 (evenIsometry d) hEE
  have hinvO := (subspace_gap_isometry_invariance_and_twirl d).2.1 (oddIsometry d) hOO
  have hcomm_proj (U : Matrix (ZMod d) (ZMod d) ℂ) (hUp : U * parityMatrix d = parityMatrix d * U) :
      U * (evenIsometry d * (evenIsometry d)ᴴ) = (evenIsometry d * (evenIsometry d)ᴴ) * U ∧
      U * (oddIsometry d * (oddIsometry d)ᴴ) = (oddIsometry d * (oddIsometry d)ᴴ) * U := by
    rw [hprojE, hprojO]; unfold evenProjector oddProjector
    exact ⟨by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, hUp], by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hUp]⟩
  have hFE (x y : ZMod d) := let ⟨c, hc, h⟩ := hF_a x y
    hinvE.2 (dftMatrix d) (x, y) (-y, x) c hF_u (hcomm_proj _ hF_p).1 h hc
  have hFO (x y : ZMod d) := let ⟨c, hc, h⟩ := hF_a x y
    hinvO.2 (dftMatrix d) (x, y) (-y, x) c hF_u (hcomm_proj _ hF_p).2 h hc
  have hSE (x y : ZMod d) := let ⟨c, hc, h⟩ := hS_a x y
    hinvE.2 (quadPhaseMatrix d) (x, y) (x, x + y) c hS_u (hcomm_proj _ hS_p).1 h hc
  have hSO (x y : ZMod d) := let ⟨c, hc, h⟩ := hS_a x y
    hinvO.2 (quadPhaseMatrix d) (x, y) (x, x + y) c hS_u (hcomm_proj _ hS_p).2 h hc
  have hstepL {M : ZMod d × ZMod d → ℂ} (hF : ∀ x y, M (x, y) = M (-y, x))
      (hS : ∀ x y, M (x, y) = M (x, x + y)) (u v : ZMod d) : M (u + v, v) = M (u, v) := by
    calc M (u + v, v) = M (-v, -v + (u + v)) := (hF (u + v) v).trans (hS (-v) (u + v))
      _ = M (-v, u) := by rw [(by ring : -v + (u + v) = u)]
      _ = M (-(-u), -(-v)) := ((hF (-v) u).trans (hF (-u) (-v))).trans (hF (-(-v)) (-u))
      _ = M (u, v) := by simp
  have heuclid (M : ZMod d × ZMod d → ℂ) (hF : ∀ x y, M (x, y) = M (-y, x))
      (hS : ∀ x y, M (x, y) = M (x, x + y)) : ∀ s u v : ℕ, u + v = s →
        M ((u : ZMod d), (v : ZMod d)) = M (0, (Nat.gcd u v : ZMod d)) := by
    intro s; induction s using Nat.strong_induction_on with | h s ih =>
      intro u v hs; by_cases hu0 : u = 0 <;> [(subst hu0; simp); by_cases hv0 : v = 0]
      · subst hv0; simpa using hF (u : ZMod d) 0
      · by_cases huv : u ≤ v
        · rw [show (v : ZMod d) = (u : ZMod d) + ((v - u : ℕ) : ZMod d) by
              rw [← Nat.cast_add, Nat.add_sub_of_le huv], ← hS _ _,
            ih (u + (v - u)) (by omega) u (v - u) rfl, Nat.gcd_sub_self_right huv]
        · have hvu : v ≤ u := by omega
          rw [show (u : ZMod d) = ((u - v : ℕ) : ZMod d) + (v : ZMod d) by
              rw [← Nat.cast_add, Nat.sub_add_cancel hvu], hstepL hF hS _ _,
            ih ((u - v) + v) (by omega) (u - v) v rfl, Nat.gcd_sub_self_left hvu]
  refine ⟨⟨hinvE.1, hinvO.1⟩, fun a _ => ⟨(Nat.gcd a.1.val a.2.val : ℤ),
    Nat.gcd_assoc a.1.val a.2.val d,
    by simpa [ZMod.natCast_zmod_val] using heuclid _ hFE hSE _ a.1.val a.2.val rfl,
    by simpa [ZMod.natCast_zmod_val] using heuclid _ hFO hSO _ a.1.val a.2.val rfl⟩⟩
private theorem exp_zpow (w : ℂ) (z : ℤ) : Complex.exp w ^ z = Complex.exp ((z : ℂ) * w) := by
  cases z with | ofNat n => simp [← Complex.exp_nat_mul] | negSucc n =>
    rw [zpow_negSucc, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
private theorem windowRoot_cos_bridge {d : ℕ} [NeZero d] (h : ℤ) (k : ℕ) :
    (2 : ℂ)⁻¹ * (windowRoot d ^ ((h : ZMod d) * (k : ZMod d)).val +
      windowRoot d ^ ((h : ZMod d) * (-(k : ZMod d))).val) =
      (Real.cos (2 * Real.pi * (h : ℝ) * (k : ℝ) / (d : ℝ)) : ℂ) := by
  have hw_z (z : ℤ) : windowRoot d ^ (z : ZMod d).val =
      Complex.exp ((z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ))) := by
    have hw_ne := (windowRoot_isPrimitiveRoot d).ne_zero (NeZero.ne d)
    have hmod : windowRoot d ^ z = windowRoot d ^ (z : ZMod d).val := by
      conv_lhs => rw [← Int.emod_add_mul_ediv z (d : ℤ)]
      rw [zpow_add₀ hw_ne, zpow_mul, zpow_natCast, (windowRoot_isPrimitiveRoot d).pow_eq_one,
        one_zpow, mul_one, ← ZMod.val_intCast (n := d) z, zpow_natCast]
    rw [← hmod]; unfold windowRoot; exact exp_zpow _ z
  rw [(by push_cast; rfl : ((h : ZMod d) * (k : ZMod d)) = ((h * (k : ℤ) : ℤ) : ZMod d)),
    (by push_cast; ring : ((h : ZMod d) * (-(k : ZMod d))) = ((-(h * (k : ℤ)) : ℤ) : ZMod d)),
    hw_z (h * (k : ℤ)), hw_z (-(h * (k : ℤ)))]
  set θ : ℝ := 2 * Real.pi * (h : ℝ) * (k : ℝ) / (d : ℝ)
  rw [show ((h * (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) =
        (θ : ℂ) * Complex.I by dsimp [θ]; push_cast; ring,
      show ((-(h * (k : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) =
        -((θ : ℂ) * Complex.I) by dsimp [θ]; push_cast; ring,
      Complex.ofReal_cos, Complex.cos, ← neg_mul]; ring
private theorem order_divisibility {d : ℕ} [NeZero d] (hd : Odd d) {h : ℤ}
    (hh : (h : ZMod d) ≠ 0) (s : ℕ) : ((s : ZMod d) * (h : ZMod d) = 0 ↔ (d / Int.gcd h d) ∣ s) ∧
      3 ≤ d / Int.gcd h d ∧ Odd (d / Int.gcd h d) := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ, Int.gcd h d = g := ⟨_, rfl⟩; rw [hg_def]; set n : ℕ := d / g
  have hg_z : (Int.gcd h (d : ℤ) : ℤ) = (g : ℤ) := by exact_mod_cast hg_def
  have hg_dvd_d : g ∣ d := Int.ofNat_dvd.mp (hg_z ▸ Int.gcd_dvd_right h (d : ℤ))
  have hg_dvd_h : (g : ℤ) ∣ h := hg_z ▸ Int.gcd_dvd_left h (d : ℤ)
  have hgn : g * n = d := Nat.mul_div_cancel' hg_dvd_d
  have hn_odd : Odd n := (Nat.even_or_odd n).resolve_left fun ⟨k, hk⟩ => by
    rcases hd with ⟨m, hdm⟩
    exact (Nat.not_even_iff_odd.mpr ⟨m, hdm⟩) ⟨g * k, by rw [← hgn, hk]; ring⟩
  have hn3 : 3 ≤ n := by rcases hn_odd with ⟨k, hk⟩; by_cases hk0 : k = 0 <;> [skip; omega]; (
    exfalso; apply hh
    have hgd : (g : ℤ) = (d : ℤ) := by exact_mod_cast (by rw [← hgn, (by omega : n = 1), mul_one])
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd h d).mpr (hgd ▸ hg_dvd_h))
  refine ⟨?_, hn3, hn_odd⟩
  rw [(by push_cast; rfl : (s : ZMod d) * (h : ZMod d) = (((s : ℤ) * h : ℤ) : ZMod d)),
    ZMod.intCast_zmod_eq_zero_iff_dvd]; rcases hg_dvd_h with ⟨h', hh'⟩
  have hg_ne : (g : ℤ) ≠ 0 :=
    by exact_mod_cast (Nat.pos_of_dvd_of_pos hg_dvd_d (Nat.pos_of_ne_zero (NeZero.ne d))).ne'
  have hd_z : (d : ℤ) = (g : ℤ) * (n : ℤ) := by exact_mod_cast hgn.symm
  refine ⟨fun ⟨q, hq⟩ => ?_,
    fun ⟨q, hsq⟩ => ⟨(q : ℤ) * h', by rw [hsq, hh', hd_z]; push_cast; ring⟩⟩
  have hdvd' : (n : ℤ) ∣ (s : ℤ) * h' := ⟨q, mul_left_cancel₀ hg_ne
    (by calc (g : ℤ) * ((s : ℤ) * h') = (s : ℤ) * ((g : ℤ) * h') := by ring
      _ = (g : ℤ) * ((n : ℤ) * q) := by rw [← hh', hq, hd_z]; ring)⟩
  let aA : ℤ := Int.gcdA h (d : ℤ); let bB : ℤ := Int.gcdB h (d : ℤ)
  have h1 : 1 = h' * aA + (n : ℤ) * bB := mul_left_cancel₀ hg_ne
    (by calc (g : ℤ) * 1 = h * aA + (d : ℤ) * bB :=
          (mul_one _).trans (hg_z.symm.trans (Int.gcd_eq_gcd_ab h (d : ℤ)))
      _ = (g : ℤ) * (h' * aA + (n : ℤ) * bB) := by rw [hh', hd_z]; ring)
  exact Int.ofNat_dvd.mp ((show (s : ℤ) = ((s : ℤ) * h') * aA + (n : ℤ) * ((s : ℤ) * bB) by
    calc (s : ℤ) = (s : ℤ) * 1 := (mul_one _).symm
      _ = _ := by rw [h1]; ring) ▸ dvd_add (dvd_mul_of_dvd_left hdvd' _) (dvd_mul_right _ _))
private theorem half_sum_pows {u v : ℂ} (huv : u * v = 1) :
    ((2 : ℂ)⁻¹ * (u + v)) ^ 2 = (4 : ℂ)⁻¹ * (u ^ 2 + 2 + v ^ 2) ∧
    ((2 : ℂ)⁻¹ * (u + v)) ^ 3 = (8 : ℂ)⁻¹ * (u ^ 3 + 3 * u ^ 1 + 3 * v ^ 1 + v ^ 3) ∧
    ((2 : ℂ)⁻¹ * (u + v)) ^ 4 = (16 : ℂ)⁻¹ * (u ^ 4 + 4 * u ^ 2 + 6 + 4 * v ^ 2 + v ^ 4) :=
  ⟨by linear_combination (2 : ℂ) * (4 : ℂ)⁻¹ * huv,
   by linear_combination (3 : ℂ) * (8 : ℂ)⁻¹ * (u + v) * huv,
   by linear_combination (16 : ℂ)⁻¹ * (4 * u ^ 2 + 6 * (u * v + 1) + 4 * v ^ 2) * huv⟩

/-- Diagonal cosine compressions of pure clock operators on the even and odd parity sectors, and
closed-form first through fourth power sums for every nonzero clock exponent modulo `d`. -/
theorem parity_clock_compression_and_power_sums
    (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) (h : ℤ) :
    ((evenIsometry d)ᴴ * paperDisplacement d (0, (h : ZMod d)) * evenIsometry d =
        Matrix.diagonal (fun idx => (evenClockDiag d h idx : ℂ)) ∧
      (oddIsometry d)ᴴ * paperDisplacement d (0, (h : ZMod d)) * oddIsometry d =
        Matrix.diagonal (fun idx => (oddClockDiag d h idx : ℂ))) ∧
    ((h : ZMod d) ≠ 0 → let n := d / Int.gcd h d
      (evenClockPowerSum d h 1 = 1 / 2 ∧ oddClockPowerSum d h 1 = -1 / 2) ∧
      (evenClockPowerSum d h 2 = ((d : ℝ) + 2) / 4 ∧ oddClockPowerSum d h 2 = ((d : ℝ) - 2) / 4) ∧
      (evenClockPowerSum d h 3 = (if n = 3 then ((d : ℝ) + 4) / 8 else 1 / 2) ∧
        oddClockPowerSum d h 3 = (if n = 3 then ((d : ℝ) - 4) / 8 else -1 / 2)) ∧
      (evenClockPowerSum d h 4 = (3 * (d : ℝ) + 8) / 16 ∧
        oddClockPowerSum d h 4 = (3 * (d : ℝ) - 8) / 16)) := by
  let diag : ZMod d → ℂ := fun r => windowRoot d ^ ((h : ZMod d) * r).val
  have hdisp_diag : paperDisplacement d (0, (h : ZMod d)) = Matrix.diagonal diag := by
    unfold paperDisplacement displacement clockMatrix
    simp only [ZMod.val_zero, zero_mul, pow_zero, one_smul, one_mul, Matrix.diagonal_pow]
    congr 1; funext r; dsimp [diag]
    rw [ZMod.val_mul, mul_comm (h : ZMod d).val r.val, windowRoot_pow_mod_nat, pow_mul]
  obtain ⟨hcompE, hcompO⟩ := sector_diagonal_compression hd diag
  have hdiagE : (evenIsometry d)ᴴ * paperDisplacement d (0, (h : ZMod d)) * evenIsometry d =
      Matrix.diagonal (fun idx => (evenClockDiag d h idx : ℂ)) := by
    rw [hdisp_diag, hcompE]; congr 1; funext idx; unfold evenClockDiag
    by_cases h0 : idx.val = 0 <;> [simp [h0, diag];
      (simp only [h0, ↓reduceIte, diag]; exact windowRoot_cos_bridge h idx.val)]
  have hdiagO : (oddIsometry d)ᴴ * paperDisplacement d (0, (h : ZMod d)) * oddIsometry d =
      Matrix.diagonal (fun idx => (oddClockDiag d h idx : ℂ)) := by
    rw [hdisp_diag, hcompO]; congr 1; funext idx; unfold oddClockDiag; dsimp [diag]
    exact windowRoot_cos_bridge h (idx.val + 1)
  refine ⟨⟨hdiagE, hdiagO⟩, fun hh => ?_⟩; intro n
  let u : ZMod d → ℂ := fun r => windowRoot d ^ ((h : ZMod d) * r).val
  let v : ZMod d → ℂ := fun r => windowRoot d ^ (-((h : ZMod d) * r)).val
  let c : ZMod d → ℂ := fun r => (2 : ℂ)⁻¹ * (u r + v r)
  have hsolve (m : ℕ) (t : ℝ) (ht : (∑ r : ZMod d, (c r) ^ m) = (t : ℂ)) :
      evenClockPowerSum d h m = (t + 1) / 2 ∧ oddClockPowerSum d h m = (t - 1) / 2 := by
    have hc_neg (r : ZMod d) : c (-r) = c r := by
      dsimp [c, u, v]; rw [(by ring : (h : ZMod d) * -r = -((h : ZMod d) * r)), neg_neg, add_comm]
    have hc_idx (j : ℕ) : c ((j + 1 : ℕ) : ZMod d) =
        (Real.cos (2 * Real.pi * (h : ℝ) * ((j + 1 : ℕ) : ℝ) / (d : ℝ)) : ℂ) := by
      rw [← windowRoot_cos_bridge h (j + 1)]; dsimp [c, u, v]; rw [mul_neg]
    have hodd_c : (oddClockPowerSum d h m : ℂ) =
        ∑ j ∈ Finset.range ((d - 1) / 2), (c ((j + 1 : ℕ) : ZMod d)) ^ m := by
      unfold oddClockPowerSum oddClockDiag; rw [Complex.ofReal_sum]; simp_rw [Complex.ofReal_pow]
      rw [Fin.sum_univ_eq_sum_range
        (fun j => (Real.cos (2 * Real.pi * (h : ℝ) * ((j + 1 : ℕ) : ℝ) / (d : ℝ)) : ℂ) ^ m)
        ((d - 1) / 2)]; exact Finset.sum_congr rfl fun j _ => by rw [hc_idx]
    have heven_c : (evenClockPowerSum d h m : ℂ) = 1 + (oddClockPowerSum d h m : ℂ) := by
      unfold evenClockPowerSum evenClockDiag; rw [Complex.ofReal_sum]; simp_rw [Complex.ofReal_pow]
      rw [Fin.sum_univ_eq_sum_range (fun j => ((if j = 0 then (1 : ℝ)
          else Real.cos (2 * Real.pi * (h : ℝ) * (j : ℝ) / (d : ℝ)) : ℝ) : ℂ) ^ m) ((d + 1) / 2),
        (by rcases hd with ⟨k, _⟩; omega : (d + 1) / 2 = (d - 1) / 2 + 1),
        Finset.sum_range_succ', hodd_c]
      simp only [↓reduceIte, Complex.ofReal_one, one_pow, Nat.succ_ne_zero, add_comm]
      exact congrArg (1 + ·) (Finset.sum_congr rfl fun j _ => by rw [hc_idx])
    have htot : (t : ℂ) = 1 + 2 * (oddClockPowerSum d h m : ℂ) := by
      rw [← ht, zmod_odd_sum_split hd (fun r => (c r) ^ m),
        (by dsimp [c, u, v]; norm_num : (c 0) ^ m = 1), hodd_c]
      simp_rw [hc_neg, ← two_mul, ← Finset.mul_sum]
    have ho : oddClockPowerSum d h m = (t - 1) / 2 :=
      Complex.ofReal_inj.mp (by push_cast; linear_combination -htot / 2)
    exact ⟨Complex.ofReal_inj.mp (by push_cast at heven_c ⊢; rw [heven_c, ho]; push_cast; ring), ho⟩
  obtain ⟨_, hn3, hn_odd⟩ := order_divisibility hd hh 1
  have hpow_zmod (x : ZMod d) (s : ℕ) :
      (windowRoot d ^ x.val) ^ s = windowRoot d ^ ((s : ZMod d) * x).val := by
    induction s with | zero => simp | succ s ih =>
      rw [pow_succ, ih, ← windowRoot_pow_val_add]; congr 2; push_cast; ring
  have hsum_uv (s : ℕ) : (∑ r : ZMod d, (u r) ^ s) = (if n ∣ s then (d : ℂ) else 0) ∧
      (∑ r : ZMod d, (v r) ^ s) = (if n ∣ s then (d : ℂ) else 0) := by
    simp_rw [show ∀ r, (u r) ^ s = windowRoot d ^ (((s : ZMod d) * (h : ZMod d)) * r).val by
        intro r; dsimp [u]; rw [hpow_zmod, mul_assoc],
      show ∀ r, (v r) ^ s = windowRoot d ^ ((-((s : ZMod d) * (h : ZMod d))) * r).val by
        intro r; dsimp [v]; rw [hpow_zmod, (by ring : (s : ZMod d) * -((h : ZMod d) * r) =
          -((s : ZMod d) * (h : ZMod d)) * r)]]
    rw [windowRoot_char_sum, windowRoot_char_sum]; by_cases hs : n ∣ s
    · simp [hs, (order_divisibility hd hh s).1.mpr hs]
    · have hz := mt (order_divisibility hd hh s).1.mp hs; simp [hs, hz, neg_ne_zero.mpr hz]
  have huv_one (r : ZMod d) : u r * v r = 1 := by
    dsimp [u, v]; rw [← windowRoot_pow_val_add, add_neg_cancel, ZMod.val_zero, pow_zero]
  have hnd1 : ¬ (n ∣ 1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega : 1 < n)
  have hnd2 : ¬ (n ∣ 2) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega : 2 < n)
  have hd3_iff : (n ∣ 3) ↔ n = 3 :=
    ⟨fun hdvd => by have := Nat.le_of_dvd (by omega) hdvd; omega, fun h => by rw [h]⟩
  have hnd4 : ¬ (n ∣ 4) := fun hdvd => by
    have := Nat.le_of_dvd (by omega) hdvd; rcases hn_odd with ⟨k, hk⟩
    rw [(by omega : n = 3)] at hdvd; omega
  obtain ⟨he1, ho1⟩ := hsolve 1 0 (by
    simp_rw [pow_one, show ∀ r, c r = (2 : ℂ)⁻¹ * ((u r) ^ 1 + (v r) ^ 1) by intro r; simp [c],
      ← Finset.mul_sum, Finset.sum_add_distrib, (hsum_uv 1).1, (hsum_uv 1).2]; simp [hnd1])
  obtain ⟨he2, ho2⟩ := hsolve 2 ((d : ℝ) / 2) (by
    dsimp only [c]; simp_rw [fun r => (half_sum_pows (huv_one r)).1, ← Finset.mul_sum,
      Finset.sum_add_distrib, (hsum_uv 2).1, (hsum_uv 2).2]
    simp [hnd2, ZMod.card]; ring)
  obtain ⟨he3, ho3⟩ := hsolve 3 (if n = 3 then (d : ℝ) / 4 else 0) (by
    dsimp only [c]; simp_rw [fun r => (half_sum_pows (huv_one r)).2.1, ← Finset.mul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum, (hsum_uv 3).1, (hsum_uv 3).2,
      (hsum_uv 1).1, (hsum_uv 1).2]
    simp only [hnd1, hd3_iff, ↓reduceIte]; split_ifs <;> push_cast <;> ring)
  obtain ⟨he4, ho4⟩ := hsolve 4 (3 * (d : ℝ) / 8) (by
    dsimp only [c]; simp_rw [fun r => (half_sum_pows (huv_one r)).2.2, ← Finset.mul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum, (hsum_uv 4).1, (hsum_uv 4).2,
      (hsum_uv 2).1, (hsum_uv 2).2]; simp [hnd4, hnd2, ZMod.card]; ring)
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by rw [he3]; split_ifs <;> ring, by rw [ho3]; split_ifs <;> ring⟩, ⟨by linarith, by linarith⟩⟩
private theorem diagonal_real_fourth_moment {d n : ℕ} [NeZero d] (hn : 1 ≤ n) (f : Fin n → ℝ) :
    Matrix.trace (alt (Matrix.diagonal (fun idx => (f idx : ℂ))) * A4 (Fin n)) =
      (((((∑ idx, (f idx) ^ 1) ^ 4 + 6 * (∑ idx, (f idx) ^ 1) ^ 2 * (∑ idx, (f idx) ^ 2) +
        3 * (∑ idx, (f idx) ^ 2) ^ 2 + 8 * (∑ idx, (f idx) ^ 1) * (∑ idx, (f idx) ^ 3) +
        6 * (∑ idx, (f idx) ^ 4)) /
        ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) : ℝ) : ℂ) := by
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun idx => (f idx : ℂ))
  have hA : Aᴴ = A := by
    unfold A; rw [Matrix.diagonal_conjTranspose]; congr 1; funext idx; simp [Complex.conj_ofReal]
  have hp := (fourth_moment_cycle_and_hermitian_formula d (S := Fin n)).2.2.2.2.2.2 A hA
  simp only [Fintype.card_fin] at hp
  have htr (m : ℕ) : Matrix.trace (A ^ m) = ((∑ idx : Fin n, (f idx) ^ m : ℝ) : ℂ) := by
    unfold A; rw [Matrix.diagonal_pow]; simp [Matrix.trace]
  have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden_r : ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) ≠ 0 := by positivity
  apply mul_left_cancel₀ (by exact_mod_cast hden_r :
    ((n : ℂ) * ((n : ℂ) + 1) * ((n : ℂ) + 2) * ((n : ℂ) + 3)) ≠ 0)
  change ((n : ℂ) * ((n : ℂ) + 1) * ((n : ℂ) + 2) * ((n : ℂ) + 3)) *
    Matrix.trace (alt A * A4 (Fin n)) = _
  rw [hp, show Matrix.trace A = ((∑ idx : Fin n, (f idx) ^ 1 : ℝ) : ℂ) by simpa using htr 1,
    htr 2, htr 3, htr 4]; exact_mod_cast (mul_div_cancel₀ _ hden_r).symm
/-- Closed-form Haar fourth moment of every nonzero Weyl–Heisenberg operator on the even and odd
parity sectors, with order-`3` bifurcation. -/
theorem parity_nonzero_label_fourth_moment
    (d : ℕ) [NeZero d] (hd3 : 3 ≤ d) (hd : Odd d) (a : ZMod d × ZMod d) (ha : a ≠ (0, 0)) :
    (weylLabelOrder d a ≠ 3 →
      labelFourthMoment (evenIsometry d) a = (((3 : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 3))) : ℂ) ∧
      labelFourthMoment (oddIsometry d) a = (((3 : ℝ) / (((d : ℝ) + 1) * ((d : ℝ) + 3))) : ℂ)) ∧
    (weylLabelOrder d a = 3 → labelFourthMoment (evenIsometry d) a =
        (((3 * (d : ℝ) + 35) / (((d : ℝ) + 1) * ((d : ℝ) + 5) * ((d : ℝ) + 7))) : ℂ) ∧
      labelFourthMoment (oddIsometry d) a =
        (((3 * (d : ℝ) - 5) / (((d : ℝ) - 1) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) : ℂ)) := by
  rcases (parity_clifford_label_reduction d hd3 hd).2 a ha with ⟨h, hgcd0, hmomE, hmomO⟩
  have hgcd : Int.gcd h d = Nat.gcd a.1.val (Nat.gcd a.2.val d) := hgcd0
  have hh0 : (h : ZMod d) ≠ 0 := fun hz => by
    have hd_gcd : d ∣ Nat.gcd a.1.val (Nat.gcd a.2.val d) := hgcd ▸ Int.ofNat_dvd.mp
      (Int.dvd_coe_gcd ((ZMod.intCast_zmod_eq_zero_iff_dvd h d).mp hz) dvd_rfl)
    exact ha (Prod.ext ((ZMod.val_eq_zero a.1).mp (Nat.eq_zero_of_dvd_of_lt
        (Nat.dvd_trans hd_gcd (Nat.gcd_dvd_left _ _)) (ZMod.val_lt a.1)))
      ((ZMod.val_eq_zero a.2).mp (Nat.eq_zero_of_dvd_of_lt
        (Nat.dvd_trans hd_gcd (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)))
        (ZMod.val_lt a.2))))
  obtain ⟨⟨hdiagE, hdiagO⟩, hpows⟩ := parity_clock_compression_and_power_sums d hd3 hd h
  obtain ⟨⟨he1, ho1⟩, ⟨he2, ho2⟩, ⟨he3, ho3⟩, ⟨he4, ho4⟩⟩ := hpows hh0
  rw [show d / Int.gcd h d = weylLabelOrder d a by unfold weylLabelOrder; rw [hgcd]] at he3 ho3
  rcases hd with ⟨m, hdm⟩; have hd_c : (d : ℂ) = 2 * (m : ℂ) + 1 := by exact_mod_cast hdm
  have hkE_r : (((d + 1) / 2 : ℕ) : ℝ) = (m : ℝ) + 1 :=
    by exact_mod_cast (by omega : (d + 1) / 2 = m + 1)
  have hkO_r : (((d - 1) / 2 : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast (by omega : (d - 1) / 2 = m)
  have q0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have q1 : (m : ℂ) + 1 ≠ 0 := (by norm_cast); have q2 : (m : ℂ) + 2 ≠ 0 := (by norm_cast)
  have q3 : (m : ℂ) + 3 ≠ 0 := (by norm_cast); have q4 : (m : ℂ) + 4 ≠ 0 := (by norm_cast)
  have p1 : (d : ℂ) + 1 ≠ 0 := (by norm_cast); have p3 : (d : ℂ) + 3 ≠ 0 := (by norm_cast)
  have p5 : (d : ℂ) + 5 ≠ 0 := (by norm_cast); have p7 : (d : ℂ) + 7 ≠ 0 := (by norm_cast)
  have pm : (d : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : d ≠ 1))
  rw [hmomE, hmomO]; unfold labelFourthMoment; rw [hdiagE, hdiagO,
    diagonal_real_fourth_moment (d := d) (by omega : 1 ≤ (d + 1) / 2) (evenClockDiag d h),
    diagonal_real_fourth_moment (d := d) (by omega : 1 ≤ (d - 1) / 2) (oddClockDiag d h)]
  unfold evenClockPowerSum at he1 he2 he3 he4; unfold oddClockPowerSum at ho1 ho2 ho3 ho4
  simp only [hkE_r, hkO_r, he1, ho1, he2, ho2, he3, ho3, he4, ho4,
    show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring, show (m : ℝ) + 1 + 2 = (m : ℝ) + 3 by ring,
    show (m : ℝ) + 1 + 3 = (m : ℝ) + 4 by ring]
  refine ⟨fun hn => ⟨?_, ?_⟩, fun h3 => ⟨?_, ?_⟩⟩
  · simp only [hn, ↓reduceIte]; push_cast; field_simp [q1, q2, q3, q4, p1, p3]; rw [hd_c]; ring
  · simp only [hn, ↓reduceIte]; push_cast; field_simp [q0, q1, q2, q3, p1, p3]; rw [hd_c]; ring
  · simp only [h3, ↓reduceIte]; push_cast; field_simp [q1, q2, q3, q4, p1, p5, p7]; rw [hd_c]; ring
  · simp only [h3, ↓reduceIte]; push_cast; field_simp [q0, q1, q2, q3, pm, p1, p5]; rw [hd_c]; ring

end D5.S3.Quantum.Magic.ParitySectorMoments
