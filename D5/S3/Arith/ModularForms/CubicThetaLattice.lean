/- GID: D5/S3/Arith/ModularForms/CubicThetaLattice
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaLattice
   mirror-E: none(waiver:formal-lattice-generating-series)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: Finite Eisenstein norm fibres and explicit cubic theta residue bijections. -/

/- Escape audit unfinished for the published coordinate maps normTripling and normThird:
https://github.com/the-omega-institute/trureturing/issues/22020 -/

import Mathlib.Data.Int.Interval
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Integer lattice fibres for the cubic theta dissection.

The lattice series in this module are not identified with Euler quotients here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaLattice

/-- The positive definite binary Eisenstein norm. -/
def eisensteinNorm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2

/-- The integer exponent in the three-core lattice sum. -/
def coreExponent (p : ℤ × ℤ) : ℤ := 3 * eisensteinNorm p - 2 * p.1 - p.2

abbrev NormFiber (n : ℕ) := {p : ℤ × ℤ // eisensteinNorm p = (n : ℤ)}
abbrev CoreFiber (n : ℕ) := {p : ℤ × ℤ // coreExponent p = (n : ℤ)}

theorem norm_coercive (p : ℤ × ℤ) :
    p.1 ^ 2 + p.2 ^ 2 ≤ 2 * eisensteinNorm p := by
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (p.1 + p.2)]

theorem norm_nonneg (p : ℤ × ℤ) : 0 ≤ eisensteinNorm p := by
  have := norm_coercive p
  nlinarith [sq_nonneg p.1, sq_nonneg p.2]

theorem core_shift_norm (p : ℤ × ℤ) :
    eisensteinNorm (3 * p.1 - 1, 3 * p.2) = 3 * coreExponent p + 1 := by
  dsimp [eisensteinNorm, coreExponent]
  ring

theorem core_exponent_nonneg (p : ℤ × ℤ) : 0 ≤ coreExponent p := by
  have h := norm_nonneg (3 * p.1 - 1, 3 * p.2)
  rw [core_shift_norm] at h
  omega

instance normFiber_finite (n : ℕ) : Finite (NormFiber n) := by
  have hfinite : Set.Finite {p : ℤ × ℤ | eisensteinNorm p = (n : ℤ)} := by
    apply (Set.finite_Icc (-(2 * (n : ℤ) + 2), -(2 * (n : ℤ) + 2))
      (2 * (n : ℤ) + 2, 2 * (n : ℤ) + 2)).subset
    intro p hp
    have h := norm_coercive p
    rw [hp] at h
    have hx : p.1 ^ 2 ≤ (2 * (n : ℤ) + 2) ^ 2 := by
      nlinarith [sq_nonneg p.2, sq_nonneg (n : ℤ)]
    have hy : p.2 ^ 2 ≤ (2 * (n : ℤ) + 2) ^ 2 := by
      nlinarith [sq_nonneg p.1, sq_nonneg (n : ℤ)]
    have hx' := abs_le_of_sq_le_sq' hx (by omega)
    have hy' := abs_le_of_sq_le_sq' hy (by omega)
    exact ⟨⟨hx'.1, hy'.1⟩, ⟨hx'.2, hy'.2⟩⟩
  exact hfinite.to_subtype

instance coreFiber_finite (n : ℕ) : Finite (CoreFiber n) := by
  let f : CoreFiber n → NormFiber (3 * n + 1) := fun p =>
    ⟨(3 * p.1.1 - 1, 3 * p.1.2), by
      rw [core_shift_norm, p.2]
      push_cast
      rfl⟩
  apply Finite.of_injective f
  intro p q hpq
  have h := congrArg Subtype.val hpq
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Subtype.ext
  exact Prod.ext (by dsimp [f] at hx; omega) (by dsimp [f] at hy; omega)

/-- The norm theta series counts the complete finite integer fibres. -/
noncomputable def normTheta : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.card (NormFiber n) : ℚ)

/-- This is a lattice series; no Euler-product identity is built into its definition. -/
noncomputable def coreTheta : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.card (CoreFiber n) : ℚ)

private theorem integer_sq_ge_self (x : ℤ) : x ≤ x ^ 2 := by
  by_cases h : x ≤ 0
  · nlinarith [sq_nonneg x]
  · have : 1 ≤ x := by omega
    nlinarith [sq_nonneg (x - 1)]

theorem core_fiber_zero (p : CoreFiber 0) : p.1 = (0, 0) := by
  have he := p.2
  have hs := core_shift_norm p.1
  have hc := norm_coercive (3 * p.1.1 - 1, 3 * p.1.2)
  rw [hs, he] at hc
  have hy : p.1.2 = 0 := by
    have hb : 9 * p.1.2 ^ 2 ≤ 2 := by
      dsimp at hc
      nlinarith [sq_nonneg (3 * p.1.1 - 1)]
    have hy0 := sq_nonneg p.1.2
    have : p.1.2 ^ 2 = 0 := by omega
    exact sq_eq_zero_iff.mp this
  have hx : p.1.1 = 0 := by
    have hxq := integer_sq_ge_self p.1.1
    have hxqn := integer_sq_ge_self (-p.1.1)
    dsimp at hc
    rw [hy] at hc
    nlinarith
  exact Prod.ext hx hy

theorem theta_nonnegative_and_normalized :
    (∀ n, 0 ≤ PowerSeries.coeff n normTheta) ∧
    (∀ n, 0 ≤ PowerSeries.coeff n coreTheta) ∧
    PowerSeries.constantCoeff normTheta = 1 ∧
    PowerSeries.constantCoeff coreTheta = 1 := by
  have hnorm : Nat.card (NormFiber 0) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨(0, 0), by norm_num [eisensteinNorm]⟩, ?_⟩
    intro p
    apply Subtype.ext
    have h := norm_coercive p.1
    rw [p.2] at h
    norm_num at h
    have hx : p.1.1 = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
    have hy : p.1.2 = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
    exact Prod.ext hx hy
  have hcore : Nat.card (CoreFiber 0) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    exact ⟨⟨(0, 0), by norm_num [coreExponent, eisensteinNorm]⟩,
      fun p => Subtype.ext (core_fiber_zero p)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n; simp [normTheta]
  · intro n; simp [coreTheta]
  · simpa [← PowerSeries.coeff_zero_eq_constantCoeff, normTheta] using
      congrArg (fun x : ℕ => (x : ℚ)) hnorm
  · simpa [← PowerSeries.coeff_zero_eq_constantCoeff, coreTheta] using
      congrArg (fun x : ℕ => (x : ℚ)) hcore

open scoped PowerSeries.WithPiTopology

theorem hasSum_counted_fibers [TopologicalSpace ℚ]
    (w : ℤ × ℤ → ℤ) (hw : ∀ p, 0 ≤ w p)
    (hf : ∀ n : ℕ, Finite {p : ℤ × ℤ // w p = (n : ℤ)}) :
    HasSum (fun p => (PowerSeries.X : PowerSeries ℚ) ^ (w p).toNat)
      (PowerSeries.mk fun n => (Nat.card {p : ℤ × ℤ // w p = (n : ℤ)} : ℚ)) := by
  classical
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  let F := {p : ℤ × ℤ // w p = (n : ℤ)}
  letI : Finite F := hf n
  letI : Fintype F := Fintype.ofFinite F
  let f : ℤ × ℤ → ℚ := fun p =>
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℚ) ^ (w p).toNat)
  have hcoeff (p : F) : f p.1 = 1 := by
    have hp : (w p.1).toNat = n := by rw [p.2]; simp
    simp [f, hp]
  have hfinite : HasSum (f ∘ (Subtype.val : F → ℤ × ℤ)) (Nat.card F : ℚ) := by
    change HasSum (fun p : F => f p.1) (Nat.card F : ℚ)
    simp only [hcoeff]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card] using (hasSum_fintype (fun _ : F => (1 : ℚ)))
  rw [PowerSeries.coeff_mk]
  change HasSum f (Nat.card F : ℚ)
  apply (Subtype.val_injective.hasSum_iff ?_).1 hfinite
  intro p hp
  dsimp [f]
  rw [PowerSeries.coeff_X_pow, if_neg]
  intro hn
  apply hp
  have hcast := Int.toNat_of_nonneg (hw p)
  exact ⟨⟨p, by omega⟩, rfl⟩

/-- Both coefficient-count constructions are the actual sums of all lattice monomials. -/
theorem hasSum_lattice_theta [TopologicalSpace ℚ] :
    HasSum (fun p : ℤ × ℤ => (PowerSeries.X : PowerSeries ℚ) ^
      (eisensteinNorm p).toNat) normTheta ∧
    HasSum (fun p : ℤ × ℤ => (PowerSeries.X : PowerSeries ℚ) ^
      (coreExponent p).toNat) coreTheta := by
  exact ⟨hasSum_counted_fibers eisensteinNorm norm_nonneg normFiber_finite,
    hasSum_counted_fibers coreExponent core_exponent_nonneg coreFiber_finite⟩

theorem norm_mod_three (p : ℤ × ℤ) :
    eisensteinNorm p % 3 = if p.1 % 3 = p.2 % 3 then 0 else 1 := by
  have hx0 := Int.emod_nonneg p.1 (by norm_num : (3 : ℤ) ≠ 0)
  have hx3 := Int.emod_lt_of_pos p.1 (by norm_num : (0 : ℤ) < 3)
  have hy0 := Int.emod_nonneg p.2 (by norm_num : (3 : ℤ) ≠ 0)
  have hy3 := Int.emod_lt_of_pos p.2 (by norm_num : (0 : ℤ) < 3)
  interval_cases hx : p.1 % 3 <;> interval_cases hy : p.2 % 3 <;>
    norm_num [eisensteinNorm, pow_two, Int.add_emod, Int.mul_emod, hx, hy]

def normTripling (p : ℤ × ℤ) : ℤ × ℤ := (p.1 - p.2, p.1 + 2 * p.2)

def normThird (p : ℤ × ℤ) : ℤ × ℤ :=
  ((2 * p.1 + p.2) / 3, (p.2 - p.1) / 3)

private theorem norm_tripling (p : ℤ × ℤ) :
    eisensteinNorm (normTripling p) = 3 * eisensteinNorm p := by
  dsimp [eisensteinNorm, normTripling]
  ring

private theorem norm_third_inverse (p : ℤ × ℤ) (h : p.1 % 3 = p.2 % 3) :
    normTripling (normThird p) = p := by
  apply Prod.ext <;> dsimp [normTripling, normThird] <;> omega

/-- Multiplication by an Eisenstein integer of norm three identifies these fibres. -/
noncomputable def normTripleEquiv (n : ℕ) : NormFiber n ≃ NormFiber (3 * n) where
  toFun p := ⟨normTripling p.1, by rw [norm_tripling, p.2]; push_cast; rfl⟩
  invFun p := ⟨normThird p.1, by
    have hm := norm_mod_three p.1
    rw [p.2] at hm
    have hd : p.1.1 % 3 = p.1.2 % 3 := by split_ifs at hm <;> omega
    have hi := norm_third_inverse p.1 hd
    have hn := norm_tripling (normThird p.1)
    rw [hi, p.2] at hn
    push_cast at hn
    omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp [normThird, normTripling] <;> omega
  right_inv p := by
    apply Subtype.ext
    apply norm_third_inverse
    have hm := norm_mod_three p.1
    rw [p.2] at hm
    split_ifs at hm <;> omega

private def rotate (i : Fin 6) (p : ℤ × ℤ) : ℤ × ℤ :=
  match i.val with
  | 0 => p
  | 1 => (-p.2, p.1 + p.2)
  | 2 => (-p.1 - p.2, p.1)
  | 3 => (-p.1, -p.2)
  | 4 => (p.2, -p.1 - p.2)
  | _ => (p.1 + p.2, -p.1)

private def unrotate (i : Fin 6) (p : ℤ × ℤ) : ℤ × ℤ :=
  match i.val with
  | 0 => p
  | 1 => (p.1 + p.2, -p.1)
  | 2 => (p.2, -p.1 - p.2)
  | 3 => (-p.1, -p.2)
  | 4 => (-p.1 - p.2, p.1)
  | _ => (-p.2, p.1 + p.2)

private theorem rotate_norm (i : Fin 6) (p : ℤ × ℤ) :
    eisensteinNorm (rotate i p) = eisensteinNorm p := by
  fin_cases i <;> simp [rotate, eisensteinNorm] <;> ring

private theorem unrotate_rotate (i : Fin 6) (p : ℤ × ℤ) :
    unrotate i (rotate i p) = p := by
  fin_cases i <;> apply Prod.ext <;> simp [rotate, unrotate] <;> ring

private theorem rotate_unrotate (i : Fin 6) (p : ℤ × ℤ) :
    rotate i (unrotate i p) = p := by
  fin_cases i <;> apply Prod.ext <;> simp [rotate, unrotate] <;> ring

private theorem unrotate_norm (i : Fin 6) (p : ℤ × ℤ) :
    eisensteinNorm (unrotate i p) = eisensteinNorm p := by
  rw [← rotate_norm i (unrotate i p), rotate_unrotate]

private def coreShift (p : ℤ × ℤ) : ℤ × ℤ := (3 * p.1 - 1, 3 * p.2)

private theorem shift_orbit_injective :
    Function.Injective (fun p : Fin 6 × (ℤ × ℤ) => rotate p.1 (coreShift p.2)) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hx := congrArg (fun z : ℤ × ℤ => z.1 % 3) h
  have hy := congrArg (fun z : ℤ × ℤ => z.2 % 3) h
  have hij : i = j := by
    fin_cases i <;> fin_cases j <;>
      norm_num [rotate, coreShift] at hx <;>
      norm_num [rotate, coreShift] at hy <;> rfl
  subst j
  have hh := congrArg (unrotate i) h
  rw [unrotate_rotate, unrotate_rotate] at hh
  have hpx := congrArg Prod.fst hh
  have hpy := congrArg Prod.snd hh
  have hpq : p = q := Prod.ext (by dsimp [coreShift] at hpx; omega)
    (by dsimp [coreShift] at hpy; omega)
  subst q
  rfl

private theorem residue_representative (p : ℤ × ℤ) (h : eisensteinNorm p % 3 = 1) :
    ∃ i : Fin 6, (unrotate i p).1 % 3 = 2 ∧ (unrotate i p).2 % 3 = 0 := by
  have hm := norm_mod_three p
  have hx0 := Int.emod_nonneg p.1 (by norm_num : (3 : ℤ) ≠ 0)
  have hx3 := Int.emod_lt_of_pos p.1 (by norm_num : (0 : ℤ) < 3)
  have hy0 := Int.emod_nonneg p.2 (by norm_num : (3 : ℤ) ≠ 0)
  have hy3 := Int.emod_lt_of_pos p.2 (by norm_num : (0 : ℤ) < 3)
  interval_cases hx : p.1 % 3 <;> interval_cases hy : p.2 % 3 <;>
    norm_num at hm <;> first
    | omega
    | (refine ⟨0, ?_, ?_⟩ <;> norm_num [unrotate] <;> omega)
    | (refine ⟨1, ?_, ?_⟩ <;> norm_num [unrotate] <;> omega)
    | (refine ⟨2, ?_, ?_⟩ <;> norm_num [unrotate] <;> omega)
    | (refine ⟨3, ?_, ?_⟩ <;> norm_num [unrotate] <;> omega)
    | (refine ⟨4, ?_, ?_⟩ <;> norm_num [unrotate] <;> omega)
    | (refine ⟨5, ?_, ?_⟩ <;> norm_num [unrotate] <;> omega)

private theorem shift_orbit_surjective (n : ℕ) (p : NormFiber (3 * n + 1)) :
    ∃ c : Fin 6 × CoreFiber n, rotate c.1 (coreShift c.2.1) = p.1 := by
  have hm : eisensteinNorm p.1 % 3 = 1 := by rw [p.2]; omega
  obtain ⟨i, hi1, hi2⟩ := residue_representative p.1 hm
  let q := unrotate i p.1
  let c : ℤ × ℤ := ((q.1 + 1) / 3, q.2 / 3)
  have hc : coreShift c = q := by
    apply Prod.ext <;> dsimp [c, coreShift] <;> dsimp [q] at * <;> omega
  have hce : coreExponent c = (n : ℤ) := by
    have hshift := core_shift_norm c
    change eisensteinNorm (coreShift c) = _ at hshift
    rw [hc, unrotate_norm, p.2] at hshift
    push_cast at hshift
    omega
  refine ⟨(i, ⟨c, hce⟩), ?_⟩
  change rotate i (coreShift c) = _
  rw [hc, rotate_unrotate]

/-- The six nonzero norm residues are disjoint rotated copies of the core lattice. -/
noncomputable def normCoreEquiv (n : ℕ) :
    (Fin 6 × CoreFiber n) ≃ NormFiber (3 * n + 1) :=
  Equiv.ofBijective
    (fun c => ⟨rotate c.1 (coreShift c.2.1), by
      rw [rotate_norm]
      change eisensteinNorm (3 * c.2.1.1 - 1, 3 * c.2.1.2) = _
      rw [core_shift_norm, c.2.2]
      push_cast
      rfl⟩)
    ⟨by
      intro c d h
      have hval := congrArg Subtype.val h
      have hh : (c.1, c.2.1) = (d.1, d.2.1) := shift_orbit_injective hval
      apply Prod.ext
      · exact congrArg (fun z : Fin 6 × (ℤ × ℤ) => z.1) hh
      · apply Subtype.ext
        exact congrArg (fun z : Fin 6 × (ℤ × ℤ) => z.2) hh,
      by
        intro p
        obtain ⟨c, hc⟩ := shift_orbit_surjective n p
        exact ⟨c, Subtype.ext hc⟩⟩

/-- The six complete rotated core cosets have alternating nontrivial cubic phases. -/
theorem normCoreEquiv_coordinate_residue (n : ℕ) (p : Fin 6 × CoreFiber n) :
    ((normCoreEquiv n p).1.1 - (normCoreEquiv n p).1.2) % 3 =
      if p.1.val % 2 = 0 then 2 else 1 := by
  rcases p with ⟨i, p⟩
  change ((rotate i (coreShift p.1)).1 - (rotate i (coreShift p.1)).2) % 3 =
    if i.val % 2 = 0 then 2 else 1
  fin_cases i <;> norm_num [rotate, coreShift] <;> omega

theorem norm_fiber_residue_counts (n : ℕ) :
    Nat.card (NormFiber (3 * n)) = Nat.card (NormFiber n) ∧
    Nat.card (NormFiber (3 * n + 1)) = 6 * Nat.card (CoreFiber n) ∧
    Nat.card (NormFiber (3 * n + 2)) = 0 := by
  refine ⟨(Nat.card_congr (normTripleEquiv n)).symm, ?_, ?_⟩
  · rw [← Nat.card_congr (normCoreEquiv n), Nat.card_prod]
    simp
  · have hempty : IsEmpty (NormFiber (3 * n + 2)) := ⟨by
      intro p
      have hm := norm_mod_three p.1
      rw [p.2] at hm
      split_ifs at hm <;> omega⟩
    exact Nat.card_of_isEmpty

/-- The full cubic lattice dissection, proved by the two fibre equivalences above. -/
theorem norm_theta_dissection :
    normTheta = PowerSeries.expand 3 (by decide) normTheta +
      PowerSeries.C 6 * (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta) := by
  have hzero (m : ℕ) : PowerSeries.coeff (3 * m)
      (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta) = 0 := by
    cases m with
    | zero => simp
    | succ m =>
      rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega,
        PowerSeries.coeff_succ_X_mul]
      exact PowerSeries.coeff_expand_of_not_dvd 3 (by decide) coreTheta (by omega)
  have hone (m : ℕ) : PowerSeries.coeff (3 * m + 1)
      (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta) =
        PowerSeries.coeff m coreTheta := by
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand_mul]
  have htwo (m : ℕ) : PowerSeries.coeff (3 * m + 2)
      (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta) = 0 := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 by omega,
      PowerSeries.coeff_succ_X_mul]
    exact PowerSeries.coeff_expand_of_not_dvd 3 (by decide) coreTheta (by omega)
  apply PowerSeries.ext
  intro n
  have hc : (∃ m, n = 3 * m) ∨ (∃ m, n = 3 * m + 1) ∨ (∃ m, n = 3 * m + 2) := by
    have hlt := Nat.mod_lt n (by decide : 0 < 3)
    by_cases h0 : n % 3 = 0
    · exact Or.inl ⟨n / 3, by omega⟩
    by_cases h1 : n % 3 = 1
    · exact Or.inr (Or.inl ⟨n / 3, by omega⟩)
    · exact Or.inr (Or.inr ⟨n / 3, by omega⟩)
  rcases hc with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand_mul, hzero]
    simpa [normTheta] using congrArg (fun x : ℕ => (x : ℚ))
      (norm_fiber_residue_counts m).1
  · rw [map_add, PowerSeries.coeff_C_mul, hone,
      PowerSeries.coeff_expand_of_not_dvd 3 (by decide) normTheta (by omega)]
    simpa [normTheta, coreTheta] using congrArg (fun x : ℕ => (x : ℚ))
      (norm_fiber_residue_counts m).2.1
  · rw [map_add, PowerSeries.coeff_C_mul, htwo,
      PowerSeries.coeff_expand_of_not_dvd 3 (by decide) normTheta (by omega)]
    simpa [normTheta] using congrArg (fun x : ℕ => (x : ℚ))
      (norm_fiber_residue_counts m).2.2

end D5.S3.Arith.ModularForms.CubicThetaLattice
