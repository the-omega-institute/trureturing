/- GID: D5/S3/Combinatorics/Matroids/PrimePowerPivotBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrimePowerPivotBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Integral basis concentration modulo a positive prime power. -/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Transvection.Basic

/-! One coordinate divides all weights modulo a prime power. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PrimePowerPivotBasis

open Finset

private theorem primary_pivot_weights {I : Type*} [Fintype I] [Nonempty I]
    (w : I → ℕ) (hwpos : ∃ i, w i ≠ 0) {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ∃ x : I, ∃ v : I → ℤ, w x ≠ 0 ∧ v x = 1 ∧
      ∀ i, ((p ^ a : ℕ) : ℤ) ∣ ((w x : ℤ) * v i - (w i : ℤ)) := by
  classical
  let m := p ^ a
  letI : NeZero m := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨g, hw, hg⟩ := (univ : Finset I).extract_gcd w univ_nonempty
  have hx : ∃ x : I, ¬ p ∣ g x := by
    by_contra! h
    have hp1 := Finset.dvd_gcd (s := (univ : Finset I)) (f := g) (fun i _ => h i)
    rw [hg] at hp1
    exact hp.not_dvd_one hp1
  obtain ⟨x, hx⟩ := hx
  have hgcd : (univ : Finset I).gcd w ≠ 0 := by
    obtain ⟨i, hi⟩ := hwpos
    intro he
    have := (Finset.gcd_eq_zero_iff.mp he) i (mem_univ i)
    exact hi this
  have hxpos : w x ≠ 0 := by
    rw [hw x (mem_univ x)]
    exact mul_ne_zero hgcd (fun he => hx (he ▸ dvd_zero p))
  let u : (ZMod m)ˣ := ((ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).2 hx).unit
  have hu : (u : ZMod m) = (g x : ZMod m) :=
    ((ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).2 hx).unit_spec
  let q (i : I) : ZMod m := (↑(u⁻¹) : ZMod m) * g i
  have hq (i : I) : (g x : ZMod m) * q i = g i := by
    change (g x : ZMod m) * ((↑(u⁻¹) : ZMod m) * (g i : ZMod m)) = (g i : ZMod m)
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  let v (i : I) : ℤ := if i = x then 1 else (q i).val
  refine ⟨x, v, hxpos, by simp [v], ?_⟩
  intro i
  change (m : ℤ) ∣ ((w x : ℤ) * v i - (w i : ℤ))
  by_cases hix : i = x
  · subst i
    simp [v]
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1
    push_cast
    rw [show (v i : ZMod m) = q i by simp [v, hix, ZMod.natCast_zmod_val]]
    rw [hw x (mem_univ x), hw i (mem_univ i)]
    push_cast
    rw [mul_assoc, hq, sub_self]

/-- One integral basis change concentrates weights modulo a prime power. -/
theorem primary_pivot_basis {I M : Type*} [Fintype I] [Nonempty I] [AddCommGroup M]
    (b : Module.Basis I ℤ M) (w : I → ℕ) (hwpos : ∃ i, w i ≠ 0) {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ∃ (x : I) (b' : Module.Basis I ℤ M) (z : M),
      w x ≠ 0 ∧ (∀ i ≠ x, b' i = b i) ∧
      (w x : ℤ) • b' x - (∑ i, (w i : ℤ) • b i) = ((p ^ a : ℕ) : ℤ) • z := by
  classical
  obtain ⟨x, v, hxpos, hv, hdiv⟩ := primary_pivot_weights w hwpos hp ha
  let t := ∑ i, v i • b i
  have hcoord (i : I) : b.coord x (b i) = if i = x then 1 else 0 := b.repr_self_apply i x
  have ht : b.coord x t = 1 := by
    change b.coord x (∑ i, v i • b i) = 1
    simp [map_sum, hcoord, hv, mul_ite]
  have hzero : b.coord x (t - b x) = 0 := by
    rw [map_sub, ht, hcoord, if_pos rfl, sub_self]
  let b' := b.map (LinearEquiv.transvection hzero)
  have hb' (i : I) : b' i = b i + b.coord x (b i) • (t - b x) := by
    rw [show b' i = LinearEquiv.transvection hzero (b i) by simp [b']]
    exact LinearEquiv.transvection.apply hzero (b i)
  have hx : b' x = t := by rw [hb', hcoord, if_pos rfl, one_smul]; abel
  choose delta hdelta using hdiv
  refine ⟨x, b', ∑ i, delta i • b i, hxpos, fun i hi => by simp [hb', hcoord, hi], ?_⟩
  rw [hx]
  change (w x : ℤ) • (∑ i, v i • b i) - ∑ i, (w i : ℤ) • b i = _
  simp_rw [smul_sum, smul_smul, ← Finset.sum_sub_distrib, ← sub_smul, hdelta]


end D5.S3.Combinatorics.Matroids.PrimePowerPivotBasis
