/- GID: D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Primitive Fibonacci states have one zero phase at each prime-power precision. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S3.Arith.FibonacciAtomic.SamplingQuotient
import D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels

open GraftAffineClosure (step)
open TimeSampling (readout zeroRank)

private theorem iterate_coprime {R : Type*} [CommRing R] (x : R × R)
    (hx : IsCoprime x.1 x.2) (i : ℕ) :
    IsCoprime (step^[i] x).1 (step^[i] x).2 := by
  induction i with
  | zero => exact hx
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    simpa only [step, mul_one] using ih.symm.add_mul_left_right (1 : R)

/-- Every primitive state that hits zero has exactly one zero phase. -/
theorem primitive_hit_phase (p m : ℕ) (hp : p.Prime)
    (x : ZMod (p ^ m) × ZMod (p ^ m)) (hx : IsUnit x.1 ∨ IsUnit x.2)
    (t k : ℕ) (ht : (step^[t] x).1 = 0) :
    (step^[k] x).1 = 0 ↔ k % zeroRank (p ^ m) = t % zeroRank (p ^ m) := by
  classical
  let n := p ^ m
  let : NeZero n := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : IsCoprime x.1 x.2 := by
    rcases hx with h | h
    · exact (isCoprime_zero_right.mpr h).of_isCoprime_of_dvd_right (dvd_zero _)
    · exact (isCoprime_zero_left.mpr h).of_isCoprime_of_dvd_left (dvd_zero _)
  have hit_unit : IsUnit (step^[t] x).2 := by
    have h := iterate_coprime x hcop t
    rw [ht] at h
    exact isCoprime_zero_left.mp h
  have ranks := (PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p 2 hp le_rfl).1 m
  have entry (i : ℕ) : (Nat.fib i : ZMod n) = 0 ↔ zeroRank n ∣ i := by
    rw [ZMod.natCast_eq_zero_iff]
    exact D5.S3.Arith.FibonacciRank.fibonacci_entry_point ranks.1 ranks.2.1 ranks.2.2
  have first_zero (i : ℕ) (b : ZMod n) :
      (step^[i] (0, b)).1 = (Nat.fib i : ZMod n) * b := by
    have h := SamplingQuotient.readout_iterate n i (b, 0)
    change readout n i (b, 0) = (step^[i] (b, 0)).2 at h
    calc
      (step^[i] (0, b)).1 = (step^[i] (step (b, 0))).1 := by simp [step]
      _ = (step (step^[i] (b, 0))).1 := by
        rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      _ = readout n i (b, 0) := h.symm
      _ = _ := by simp [readout]
  have forward (d : ℕ) : (step^[t + d] x).1 = 0 ↔ zeroRank n ∣ d := by
    rw [Nat.add_comm t d, Function.iterate_add_apply]
    have pair : step^[t] x = (0, (step^[t] x).2) := Prod.ext ht rfl
    rw [pair, first_zero, hit_unit.mul_left_eq_zero, entry]
  let L := (n ^ 2).factorial
  have period (z : ZMod n × ZMod n) : Function.IsPeriodicPt step L z :=
    ((GraftAffineClosure.result.2 n (pow_pos hp.pos m) (0, 0)).2.1 z)
  have Lpos : 0 < L := Nat.factorial_pos _
  have rankL : zeroRank n ∣ L := by
    apply (entry L).mp
    have h := congrArg Prod.fst (period (0, 1)).eq
    rw [first_zero] at h
    simpa using h
  let q := (t + 1) * L
  have tq : t ≤ k + q := by
    have : t + 1 ≤ q := Nat.le_mul_of_pos_right _ Lpos
    omega
  have same_state : step^[k + q] x = step^[k] x := by
    rw [Function.iterate_add_apply]
    rw [((period x).const_mul (t + 1)).eq]
  have same_phase : (k + q) % zeroRank n = k % zeroRank n := by
    have hq : zeroRank n ∣ q := dvd_mul_of_dvd_right rankL _
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hq, add_zero, Nat.mod_mod]
  rw [← same_state, ← same_phase]
  change (step^[k + q] x).1 = 0 ↔ Nat.ModEq (zeroRank n) (k + q) t
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' tq]
  rw [← forward (k + q - t), Nat.add_sub_cancel' tq]

/-- Reduction of a residue pair to a specified prime-power precision. -/
def reducePair (p H i : ℕ) (x : ZMod (p ^ H) × ZMod (p ^ H)) :
    ZMod (p ^ i) × ZMod (p ^ i) := (ZMod.cast x.1, ZMod.cast x.2)

/-- The highest precision, up to the cutoff, at which the first coordinate hits zero. -/
noncomputable def topHit (p H m : ℕ) (x : ZMod (p ^ H) × ZMod (p ^ H)) : ℕ := by
  classical
  exact Nat.findGreatest (fun i => ∃ k : ℕ, (step^[k] (reducePair p H i x)).1 = 0) m

/-- A primitive direction is its orbit under simultaneous multiplication by a unit. -/
def direction (p H i : ℕ) (x : ZMod (p ^ H) × ZMod (p ^ H)) :
    Set (ZMod (p ^ i) × ZMod (p ^ i)) :=
  MulAction.orbit (ZMod (p ^ i))ˣ (reducePair p H i x)

/-- Below a layer with no zero hit, the complete divisibility profile is exactly
its highest hit layer and the primitive direction at that layer. -/
theorem primitive_no_hit_profile (p H m : ℕ) (hp : p.Prime) (hm : m ≤ H)
    (x y : ZMod (p ^ H) × ZMod (p ^ H))
    (hx : IsUnit x.1 ∨ IsUnit x.2) (hy : IsUnit y.1 ∨ IsUnit y.2)
    (nx : ¬ ∃ k : ℕ, (step^[k] (reducePair p H m x)).1 = 0)
    (ny : ¬ ∃ k : ℕ, (step^[k] (reducePair p H m y)).1 = 0) :
    (∀ k i : ℕ, i ≤ m →
      ((step^[k] (reducePair p H i x)).1 = 0 ↔
        (step^[k] (reducePair p H i y)).1 = 0)) ↔
    ∃ j : ℕ, j < m ∧ topHit p H m x = j ∧ topHit p H m y = j ∧
      direction p H j x = direction p H j y := by
  classical
  let hit (z : ZMod (p ^ H) × ZMod (p ^ H)) (i : ℕ) :=
    ∃ k : ℕ, (step^[k] (reducePair p H i z)).1 = 0
  have top_le (z : ZMod (p ^ H) × ZMod (p ^ H)) : topHit p H m z ≤ m :=
    Nat.findGreatest_le m
  have top_lt (z : ZMod (p ^ H) × ZMod (p ^ H)) (nz : ¬ hit z m) :
      topHit p H m z < m := by
    have hle := top_le z
    by_contra h
    have eq : topHit p H m z = m := by omega
    by_cases hm0 : m = 0
    · subst m
      let : Subsingleton (ZMod (p ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact nz ⟨0, Subsingleton.elim _ _⟩
    · exact nz (Nat.findGreatest_of_ne_zero eq hm0)
  have reduced_primitive (z : ZMod (p ^ H) × ZMod (p ^ H))
      (hz : IsUnit z.1 ∨ IsUnit z.2) (i : ℕ) (hi : i ≤ H) :
      IsUnit (reducePair p H i z).1 ∨ IsUnit (reducePair p H i z).2 := by
    let f := ZMod.castHom (pow_dvd_pow p hi) (ZMod (p ^ i))
    exact hz.imp (fun h => h.map f) (fun h => h.map f)
  have hit_unit (i k : ℕ) (z : ZMod (p ^ i) × ZMod (p ^ i))
      (hz : IsUnit z.1 ∨ IsUnit z.2) (zero : (step^[k] z).1 = 0) :
      IsUnit (step^[k] z).2 := by
    have cop : IsCoprime z.1 z.2 := by
      rcases hz with h | h
      · exact (isCoprime_zero_right.mpr h).of_isCoprime_of_dvd_right (dvd_zero _)
      · exact (isCoprime_zero_left.mpr h).of_isCoprime_of_dvd_left (dvd_zero _)
    have h := iterate_coprime z cop k
    rw [zero] at h
    exact isCoprime_zero_left.mp h
  have scale_iter (i k : ℕ) (u : (ZMod (p ^ i))ˣ)
      (z : ZMod (p ^ i) × ZMod (p ^ i)) :
      u • (step^[k] z) = step^[k] (u • z) := by
    have semiconj : Function.Semiconj (fun z : ZMod (p ^ i) × ZMod (p ^ i) => u • z)
        step step := by
      intro z
      ext <;> simp [step, smul_add]
    exact semiconj.iterate_right k z
  have kernel_direction (i k : ℕ) (hi : i ≤ H)
      (zx : (step^[k] (reducePair p H i x)).1 = 0)
      (zy : (step^[k] (reducePair p H i y)).1 = 0) :
      direction p H i x = direction p H i y := by
    let X := reducePair p H i x
    let Y := reducePair p H i y
    have ux := hit_unit i k X (reduced_primitive x hx i hi) zx
    have uy := hit_unit i k Y (reduced_primitive y hy i hi) zy
    let u := ux.unit * uy.unit⁻¹
    have at_hit : step^[k] X = u • (step^[k] Y) := by
      apply Prod.ext
      · change (step^[k] X).1 = (u : ZMod (p ^ i)) * (step^[k] Y).1
        change (step^[k] X).1 = 0 at zx
        change (step^[k] Y).1 = 0 at zy
        rw [zx, zy, mul_zero]
      · change (step^[k] X).2 = (u : ZMod (p ^ i)) * (step^[k] Y).2
        rw [← ux.unit_spec, ← uy.unit_spec]
        simp [u, mul_assoc]
    have period (z : ZMod (p ^ i) × ZMod (p ^ i)) :
        Function.IsPeriodicPt step ((p ^ i) ^ 2).factorial z :=
      ((GraftAffineClosure.result.2 (p ^ i) (pow_pos hp.pos i) (0, 0)).2.1 z)
    have relation : X = u • Y :=
      ((period X).iterate k).eq_of_apply_eq_same ((period (u • Y)).iterate k)
        (Nat.factorial_pos _) (at_hit.trans (scale_iter i k u Y))
    exact MulAction.orbit_eq_iff.mpr (MulAction.mem_orbit_iff.mpr ⟨u, relation.symm⟩)
  have reduce_comp (i j : ℕ) (hij : i ≤ j) (hj : j ≤ H)
      (z : ZMod (p ^ H) × ZMod (p ^ H)) :
      reducePair p H i z =
        ((ZMod.castHom (pow_dvd_pow p hij) (ZMod (p ^ i))) (reducePair p H j z).1,
         (ZMod.castHom (pow_dvd_pow p hij) (ZMod (p ^ i))) (reducePair p H j z).2) := by
    apply Prod.ext
    · exact (DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow p hij)
        (pow_dvd_pow p hj)) z.1).symm
    · exact (DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow p hij)
        (pow_dvd_pow p hj)) z.2).symm
  constructor
  · intro profile
    let j := topHit p H m x
    have hj : j < m := top_lt x nx
    have same_top : topHit p H m x = topHit p H m y := by
      apply Nat.le_antisymm
      · by_cases hj0 : topHit p H m x = 0
        · simp [hj0]
        · apply Nat.le_findGreatest (top_le x)
          obtain ⟨k, hk⟩ := Nat.findGreatest_of_ne_zero rfl hj0
          exact ⟨k, (profile k _ (top_le x)).mp hk⟩
      · by_cases hj0 : topHit p H m y = 0
        · simp [hj0]
        · apply Nat.le_findGreatest (top_le y)
          obtain ⟨k, hk⟩ := Nat.findGreatest_of_ne_zero rfl hj0
          exact ⟨k, (profile k _ (top_le y)).mpr hk⟩
    refine ⟨j, hj, rfl, same_top.symm, ?_⟩
    by_cases hj0 : j = 0
    · rw [hj0]
      let : Subsingleton (ZMod (p ^ 0)) := by
        rw [pow_zero]
        infer_instance
      exact congrArg (MulAction.orbit (ZMod (p ^ 0))ˣ) (Subsingleton.elim _ _)
    · obtain ⟨k, hk⟩ := Nat.findGreatest_of_ne_zero rfl hj0
      exact kernel_direction j k (hj.le.trans hm) hk ((profile k j hj.le).mp hk)
  · rintro ⟨j, hj, tx, ty, directions⟩ k i hi
    by_cases hij : i ≤ j
    · obtain ⟨u, hu⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbit_eq_iff.mp directions)
      let f := ZMod.castHom (pow_dvd_pow p hij) (ZMod (p ^ i))
      let v := Units.map f.toMonoidHom u
      have lower : reducePair p H i x = v • reducePair p H i y := by
        rw [reduce_comp i j hij (hj.le.trans hm) x, ← hu,
          reduce_comp i j hij (hj.le.trans hm) y]
        apply Prod.ext
        · change f ((u : ZMod (p ^ j)) * (reducePair p H j y).1) =
            f (u : ZMod (p ^ j)) * f (reducePair p H j y).1
          exact f.map_mul _ _
        · change f ((u : ZMod (p ^ j)) * (reducePair p H j y).2) =
            f (u : ZMod (p ^ j)) * f (reducePair p H j y).2
          exact f.map_mul _ _
      rw [lower, ← scale_iter]
      change (v : ZMod (p ^ i)) * (step^[k] (reducePair p H i y)).1 = 0 ↔ _
      exact v.isUnit.mul_right_eq_zero
    · have hxno : ¬ hit x i := Nat.findGreatest_is_greatest
        (show topHit p H m x < i by omega) hi
      have hyno : ¬ hit y i := Nat.findGreatest_is_greatest
        (show topHit p H m y < i by omega) hi
      exact iff_of_false (fun h => hxno ⟨k, h⟩) (fun h => hyno ⟨k, h⟩)

/-- The common saturated depth of a residue pair. -/
def content (p h : ℕ) (x : ZMod (p ^ h) × ZMod (p ^ h)) : ℕ :=
  min (D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (x.1.val : ℤ))
    (D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (x.2.val : ℤ))

/-- Normalize both coordinates using the existing affine residue coordinates. -/
def scaledPair (p h s : ℕ) (x : ZMod (p ^ h) × ZMod (p ^ h)) :
    ZMod (p ^ (h - s)) × ZMod (p ^ (h - s)) :=
  ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta p h s (x.1.val : ℤ)).elim
      Prod.snd id,
   (D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta p h s (x.2.val : ℤ)).elim
      Prod.snd id)

/-- High pairs retain both coordinates; low pairs retain a maximal direction
or a hit phase with the prescribed two scalar precisions. -/
inductive LocalLabel (p h e : ℕ) where
  | high (x : ZMod (p ^ h) × ZMod (p ^ h))
  | noHit (s j : ℕ) (P : Option (Set (ZMod (p ^ j) × ZMod (p ^ j))))
  | hit (s t : ℕ) (A : ZMod (p ^ h))
      (U : ZMod (p ^ (h - s - padicValInt p
        (Nat.fib (zeroRank (p ^ (e - s))) : ℤ))))

/-- The three local records use the least nonnegative hit and the full zero-rank
valuation, including stationary rank lifts and the unique residue modulo one. -/
noncomputable def localLabel (p h e : ℕ) (x : ZMod (p ^ h) × ZMod (p ^ h)) :
    LocalLabel p h e := by
  classical
  let s := content p h x
  if e ≤ s then
    exact .high x
  else
    let u := scaledPair p h s x
    let m := e - s
    if hits : ∃ k : ℕ, (step^[k] (reducePair p (h - s) m u)).1 = 0 then
      let t := Nat.find hits
      exact .hit s t (step^[t] x).1 (ZMod.cast (scaledPair p h s (step^[t] x)).2)
    else
      let j := topHit p (h - s) m u
      exact .noHit s j (if j = 0 then none else some (direction p (h - s) j u))

#print axioms primitive_hit_phase
#print axioms primitive_no_hit_profile

end D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels
