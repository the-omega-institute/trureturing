/- GID: D5/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GraftLocalBehaviorLabels
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Canonical local labels classify all future Fibonacci prime-power readings. -/

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

-- The three dependent record branches and scalar precision casts use a larger elaboration budget.
set_option maxHeartbeats 800000 in
/-- The complete classification combines dependent records, normalization, and coarse sampling. -/
theorem result (p h e : ℕ) (hp : p.Prime) (hh : 1 ≤ h) (he : e ≤ h)
    (x y : ZMod (p ^ h) × ZMod (p ^ h)) :
    (∀ k : ℕ, GraftAffineClosure.psi p h e ((step^[k] x).1.val : ℤ) =
      GraftAffineClosure.psi p h e ((step^[k] y).1.val : ℤ)) ↔
    localLabel p h e x = localLabel p h e y := by
  classical
  let : NeZero (p ^ h) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have recover_depth (a b : ZMod (p ^ h))
      (same : GraftAffineClosure.psi p h e (a.val : ℤ) =
        GraftAffineClosure.psi p h e (b.val : ℤ)) :
      D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (a.val : ℤ) =
        D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (b.val : ℤ) := by
    have equal_gcd := (GraftAffineClosure.result.1 p h e hp he
      (a.val : ℤ) (b.val : ℤ)).mpr same 0
    simpa only [D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth,
      mul_zero, add_zero] using congrArg (Nat.log p) equal_gcd
  have recover_content
      (future : ∀ k : ℕ, GraftAffineClosure.psi p h e ((step^[k] x).1.val : ℤ) =
        GraftAffineClosure.psi p h e ((step^[k] y).1.val : ℤ)) :
      content p h x = content p h y := by
    have first := recover_depth x.1 y.1 (future 0)
    have second := recover_depth x.2 y.2 (future 1)
    exact congrArg₂ min first second
  have scaled_primitive (z : ZMod (p ^ h) × ZMod (p ^ h)) :
      IsUnit (scaledPair p h (content p h z) z).1 ∨
        IsUnit (scaledPair p h (content p h z) z).2 := by
    let s := content p h z
    have d1 : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.1.val : ℤ) :=
      min_le_left _ _
    have d2 : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.2.val : ℤ) :=
      min_le_right _ _
    have quotient (a : ZMod (p ^ h)) :
        IsUnit ((a.val : ℤ) / (p : ℤ) ^
          D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (a.val : ℤ) :
          ZMod (p ^ (h - D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
            (a.val : ℤ)))) := by
      apply (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr
      simpa only [Nat.cast_pow] using
        (Int.isCoprime_iff_gcd_eq_one.mpr
          (D5.S3.Arith.Congruence.PrimePowerAffineBehavior.normalized_gcd
            p h hp (a.val : ℤ))).symm
    by_cases order : D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.1.val : ℤ) ≤
        D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.2.val : ℤ)
    · have eqs : s = D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.1.val : ℤ) :=
        min_eq_left order
      left
      change IsUnit ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta
        p h s (z.1.val : ℤ)).elim Prod.snd id)
      simp only [D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta,
        if_neg (not_lt.mpr d1), Sum.elim_inr]
      rw [eqs]
      exact quotient z.1
    · have eqs : s = D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.2.val : ℤ) :=
        min_eq_right (le_of_not_ge order)
      right
      change IsUnit ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta
        p h s (z.2.val : ℤ)).elim Prod.snd id)
      simp only [D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta,
        if_neg (not_lt.mpr d2), Sum.elim_inr]
      rw [eqs]
      exact quotient z.2
  have scaled_future (z : ZMod (p ^ h) × ZMod (p ^ h)) (k : ℕ) :
      Int.ModEq ((p : ℤ) ^ h)
        ((p : ℤ) ^ content p h z *
          ((step^[k] (scaledPair p h (content p h z) z)).1.val : ℤ))
        ((step^[k] z).1.val : ℤ) := by
    let s := content p h z
    have d1 : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.1.val : ℤ) :=
      min_le_left _ _
    have d2 : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.2.val : ℤ) :=
      min_le_right _ _
    have hs : s ≤ h := d1.trans
      (D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth_data p h hp (z.1.val : ℤ)).1
    let : NeZero (p ^ (h - s)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    let g : ℤ →+ ZMod (p ^ h) := {
      toFun := fun a => (p : ZMod (p ^ h)) ^ s * (a : ZMod (p ^ h))
      map_zero' := by simp
      map_add' := by intro a b; simp [mul_add] }
    have kernel : g (p ^ (h - s)) = 0 := by
      change (p : ZMod (p ^ h)) ^ s * ((p : ℤ) ^ (h - s) : ℤ) = 0
      rw [Int.cast_pow, Int.cast_natCast, ← pow_add, Nat.add_sub_of_le hs]
      simpa only [Nat.cast_pow] using (ZMod.natCast_self (p ^ h))
    let f : ZMod (p ^ (h - s)) →+ ZMod (p ^ h) :=
      ZMod.lift (p ^ (h - s)) ⟨g, kernel⟩
    have lift_cast (a : ℤ) :
        f (a : ZMod (p ^ (h - s))) = (p : ZMod (p ^ h)) ^ s * (a : ZMod (p ^ h)) :=
      ZMod.lift_coe _ _ _
    have lift_initial (a : ZMod (p ^ h))
        (ha : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (a.val : ℤ)) :
        f (((a.val : ℤ) / (p : ℤ) ^ s : ℤ) : ZMod (p ^ (h - s))) = a := by
      have divides := ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth_divisibility
        p h hp (a.val : ℤ) s).mpr ha).1
      rw [lift_cast, ← Int.cast_natCast p, ← Int.cast_pow, ← Int.cast_mul,
        Int.mul_ediv_cancel' divides]
      simp
    let u := scaledPair p h s z
    let φ := fun a : ZMod (p ^ (h - s)) × ZMod (p ^ (h - s)) => (f a.1, f a.2)
    have semi : Function.Semiconj φ step step := by
      intro a
      exact Prod.ext rfl (f.map_add a.1 a.2)
    have initial : φ u = z := by
      apply Prod.ext
      · change f ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta
          p h s (z.1.val : ℤ)).elim Prod.snd id) = z.1
        simp only [D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta,
          if_neg (not_lt.mpr d1), Sum.elim_inr]
        exact lift_initial z.1 d1
      · change f ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta
          p h s (z.2.val : ℤ)).elim Prod.snd id) = z.2
        simp only [D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta,
          if_neg (not_lt.mpr d2), Sum.elim_inr]
        exact lift_initial z.2 d2
    have at_time := semi.iterate_right k u
    rw [initial] at at_time
    have first : f (step^[k] u).1 = (step^[k] z).1 := congrArg Prod.fst at_time
    have cast_eq :
        (((p : ℤ) ^ s * ((step^[k] u).1.val : ℤ) : ℤ) : ZMod (p ^ h)) =
          (((step^[k] z).1.val : ℤ) : ZMod (p ^ h)) := by
      rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← lift_cast,
        Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_natCast,
        ZMod.natCast_zmod_val]
      exact first
    simpa only [Nat.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ (p ^ h)).mp cast_eq
  have normalized_zero (z : ZMod (p ^ h) × ZMod (p ^ h)) (k i : ℕ)
      (hi : i ≤ h - content p h z) :
      (step^[k] (reducePair p (h - content p h z) i
        (scaledPair p h (content p h z) z))).1 = 0 ↔
      content p h z + i ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
        ((step^[k] z).1.val : ℤ) := by
    let s := content p h z
    have hs : s ≤ h := (min_le_left _ _).trans
      (D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth_data p h hp (z.1.val : ℤ)).1
    have hsi : s + i ≤ h := by omega
    let : NeZero (p ^ (h - s)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    let u := scaledPair p h s z
    let r := ZMod.castHom (pow_dvd_pow p hi) (ZMod (p ^ i))
    let φ := fun a : ZMod (p ^ (h - s)) × ZMod (p ^ (h - s)) => (r a.1, r a.2)
    have semi : Function.Semiconj φ step step := by
      intro a
      exact Prod.ext rfl (r.map_add a.1 a.2)
    have reduced : (r (step^[k] u).1, r (step^[k] u).2) =
        step^[k] (reducePair p (h - s) i u) := semi.iterate_right k u
    have congruence := (scaled_future z k).of_dvd (pow_dvd_pow (p : ℤ) hsi)
    rw [← D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth_divisibility
      p h hp ((step^[k] z).1.val : ℤ) (s + i)]
    simp only [hsi, and_true]
    change (step^[k] (reducePair p (h - s) i u)).1 = 0 ↔ _
    rw [← congrArg Prod.fst reduced]
    change (ZMod.cast (step^[k] u).1 : ZMod (p ^ i)) = 0 ↔ _
    rw [ZMod.cast_eq_val, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_pow, ← congruence.dvd_iff, pow_add]
    exact (mul_dvd_mul_iff_left (pow_ne_zero s
      (Int.natCast_ne_zero.mpr hp.ne_zero))).symm
  have base_depth (z : ZMod (p ^ h) × ZMod (p ^ h)) (k : ℕ) :
      content p h z ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
        ((step^[k] z).1.val : ℤ) := by
    have hz := normalized_zero z k 0 (Nat.zero_le _)
    simp only [add_zero] at hz
    apply hz.mp
    have : Subsingleton (ZMod (p ^ 0)) := by simp only [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  have first_readout (k : ℕ) (z : ZMod (p ^ h) × ZMod (p ^ h)) :
      (step^[k] z).1 = readout (p ^ h) k (z.2 - z.1, z.1) := by
    have initial : step (z.2 - z.1, z.1) = z := by ext <;> simp [step]
    calc
      (step^[k] z).1 = (step^[k] (step (z.2 - z.1, z.1))).1 := by rw [initial]
      _ = (step (step^[k] (z.2 - z.1, z.1))).1 := by
        rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      _ = _ := (SamplingQuotient.readout_iterate (p ^ h) k (z.2 - z.1, z.1)).symm
  have high_scalar (a b : ZMod (p ^ h))
      (ha : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (a.val : ℤ))
      (hb : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (b.val : ℤ)) :
      GraftAffineClosure.psi p h e (a.val : ℤ) =
        GraftAffineClosure.psi p h e (b.val : ℤ) ↔ a = b := by
    simp only [GraftAffineClosure.psi, if_neg (not_lt.mpr ha),
      if_neg (not_lt.mpr hb), Sum.inr.injEq, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hit_precision (s r : ℕ) (hr : 0 < r) (a b : ZMod (p ^ h))
      (ha : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (a.val : ℤ))
      (hb : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (b.val : ℤ)) :
      (Nat.fib r : ZMod (p ^ h)) * (a - b) = 0 ↔
      (((a.val : ℤ) / (p : ℤ) ^ s : ℤ) :
        ZMod (p ^ (h - s - padicValInt p (Nat.fib r : ℤ)))) =
      (((b.val : ℤ) / (p : ℤ) ^ s : ℤ) :
        ZMod (p ^ (h - s - padicValInt p (Nat.fib r : ℤ)))) := by
    let : Fact p.Prime := ⟨hp⟩
    have da := ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth_divisibility
      p h hp (a.val : ℤ) s).mpr ha).1
    have db := ((D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth_divisibility
      p h hp (b.val : ℤ) s).mpr hb).1
    let d := (a.val : ℤ) / (p : ℤ) ^ s - (b.val : ℤ) / (p : ℤ) ^ s
    have diff : (a.val : ℤ) - b.val = (p : ℤ) ^ s * d := by
      dsimp only [d]
      rw [mul_sub, Int.mul_ediv_cancel' da, Int.mul_ediv_cancel' db]
    have hf : (Nat.fib r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.fib_pos.mpr hr).ne'
    have precision : (p : ℤ) ^ h ∣ (Nat.fib r : ℤ) * ((p : ℤ) ^ s * d) ↔
        (p : ℤ) ^ (h - s - padicValInt p (Nat.fib r : ℤ)) ∣ d := by
      by_cases hd : d = 0
      · simp only [hd, mul_zero, dvd_zero]
      have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
      have hs0 : (p : ℤ) ^ s ≠ 0 := pow_ne_zero _ hp0
      have hsd0 := mul_ne_zero hs0 hd
      have hf0 := mul_ne_zero hf hsd0
      have hsval : padicValInt p ((p : ℤ) ^ s) = s := by
        simpa only [padicValInt, Int.natAbs_pow, Int.natAbs_natCast] using
          padicValNat.prime_pow (p := p) s
      rw [padicValInt_dvd_iff, padicValInt_dvd_iff]
      simp only [hf0, hd, false_or]
      rw [padicValInt.mul hf hsd0, padicValInt.mul hs0 hd, hsval]
      omega
    have left : (Nat.fib r : ZMod (p ^ h)) * (a - b) = 0 ↔
        (p : ℤ) ^ h ∣ (Nat.fib r : ℤ) * ((p : ℤ) ^ s * d) := by
      rw [← diff]
      simpa only [Int.cast_mul, Int.cast_sub, Int.cast_natCast,
        ZMod.natCast_zmod_val, Nat.cast_pow] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd
          ((Nat.fib r : ℤ) * ((a.val : ℤ) - b.val)) (p ^ h))
    rw [left, precision, ← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
  have quotient_second (z : ZMod (p ^ h) × ZMod (p ^ h)) (s l : ℕ)
      (hl : l ≤ h - s)
      (hz : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (z.2.val : ℤ)) :
      (ZMod.cast (scaledPair p h s z).2 : ZMod (p ^ l)) =
        (((z.2.val : ℤ) / (p : ℤ) ^ s : ℤ) : ZMod (p ^ l)) := by
    simp only [scaledPair, D5.S3.Arith.Congruence.PrimePowerAffineBehavior.eta,
      if_neg (not_lt.mpr hz), Sum.elim_inr]
    exact ZMod.cast_intCast (pow_dvd_pow p hl) _
  have low_profile (z w : ZMod (p ^ h) × ZMod (p ^ h))
      (sc : content p h z = content p h w)
      (profile : ∀ k i : ℕ, i ≤ e - content p h z →
        ((step^[k] (reducePair p (h - content p h z) i
          (scaledPair p h (content p h z) z))).1 = 0 ↔
         (step^[k] (reducePair p (h - content p h w) i
          (scaledPair p h (content p h w) w))).1 = 0))
      (k : ℕ)
      (low : D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
        ((step^[k] z).1.val : ℤ) < e) :
      GraftAffineClosure.psi p h e ((step^[k] z).1.val : ℤ) =
        GraftAffineClosure.psi p h e ((step^[k] w).1.val : ℤ) := by
    let s := content p h z
    have bz := base_depth z k
    have bw := base_depth w k
    rw [← sc] at bw
    have thresholds (i : ℕ) (hi : i ≤ e) :
        (i ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
          ((step^[k] z).1.val : ℤ)) ↔
        (i ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
          ((step^[k] w).1.val : ℤ)) := by
      by_cases his : i ≤ s
      · exact iff_of_true (his.trans bz) (his.trans bw)
      · have si : s ≤ i := (Nat.lt_of_not_ge his).le
        have left := normalized_zero z k (i - s) (Nat.sub_le_sub_right (hi.trans he) s)
        have right := normalized_zero w k (i - s)
          (by rw [← sc]; exact Nat.sub_le_sub_right (hi.trans he) s)
        rw [← sc] at right
        have add : content p h z + (i - s) = i := Nat.add_sub_of_le si
        rw [add] at left right
        have prof := profile k (i - s) (Nat.sub_le_sub_right hi s)
        rw [← sc] at prof
        exact left.symm.trans (prof.trans right)
    have loww : D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
        ((step^[k] w).1.val : ℤ) < e := by
      by_contra hn
      have := (thresholds e le_rfl).mpr (le_of_not_gt hn)
      omega
    have same : D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
        ((step^[k] z).1.val : ℤ) =
        D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
          ((step^[k] w).1.val : ℤ) :=
      Nat.le_antisymm ((thresholds _ low.le).mp le_rfl) ((thresholds _ loww.le).mpr le_rfl)
    simp only [GraftAffineClosure.psi, if_pos loww, same]
  let label_content : LocalLabel p h e → ℕ := fun L => match L with
    | .high z => content p h z
    | .noHit s _ _ => s
    | .hit s _ _ _ => s
  have label_content_eq (z : ZMod (p ^ h) × ZMod (p ^ h)) :
      label_content (localLabel p h e z) = content p h z := by
    unfold localLabel
    dsimp only
    split_ifs <;> rfl
  have low_label (z : ZMod (p ^ h) × ZMod (p ^ h)) (s : ℕ)
      (hs : content p h z = s) (hl : ¬ e ≤ s) :
      localLabel p h e z =
      (if hits : ∃ k : ℕ, (step^[k] (reducePair p (h - s) (e - s)
          (scaledPair p h s z))).1 = 0 then
        LocalLabel.hit s (Nat.find hits) (step^[Nat.find hits] z).1
          (ZMod.cast (scaledPair p h s (step^[Nat.find hits] z)).2)
      else LocalLabel.noHit s (topHit p (h - s) (e - s) (scaledPair p h s z))
        (if topHit p (h - s) (e - s) (scaledPair p h s z) = 0 then none else
          some (direction p (h - s)
            (topHit p (h - s) (e - s) (scaledPair p h s z)) (scaledPair p h s z)))) := by
    subst s
    unfold localLabel
    dsimp only
    rw [dif_neg hl]
  by_cases high : e ≤ content p h x
  · have hx1 : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (x.1.val : ℤ) :=
      high.trans (min_le_left _ _)
    have hx2 : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (x.2.val : ℤ) :=
      high.trans (min_le_right _ _)
    constructor
    · intro future
      have hy : e ≤ content p h y := (recover_content future) ▸ high
      have hy1 : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (y.1.val : ℤ) :=
        hy.trans (min_le_left _ _)
      have hy2 : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h (y.2.val : ℤ) :=
        hy.trans (min_le_right _ _)
      have first : x.1 = y.1 := by
        have at0 := future 0
        simp only [Function.iterate_zero_apply, GraftAffineClosure.psi,
          if_neg (not_lt.mpr hx1), if_neg (not_lt.mpr hy1),
          Int.cast_natCast, ZMod.natCast_zmod_val, Sum.inr.injEq] at at0
        exact at0
      have second : x.2 = y.2 := by
        have at1 := future 1
        change GraftAffineClosure.psi p h e (x.2.val : ℤ) =
          GraftAffineClosure.psi p h e (y.2.val : ℤ) at at1
        simpa only [GraftAffineClosure.psi,
          if_neg (not_lt.mpr hx2), if_neg (not_lt.mpr hy2),
          Int.cast_natCast, ZMod.natCast_zmod_val, Sum.inr.injEq] using at1
      rw [Prod.ext first second]
    · intro labels
      have pair : x = y := by
        simp only [localLabel] at labels
        split_ifs at labels with hy hit
        · exact LocalLabel.high.inj labels
      subst y
      intro k
      rfl
  · constructor
    · intro future
      have same_content := recover_content future
      have lowx : content p h x < e := Nat.lt_of_not_ge high
      let s := content p h x
      let m := e - s
      have hm : m ≤ h - s := Nat.sub_le_sub_right he s
      let u := scaledPair p h s x
      let v := scaledPair p h s y
      have sy : content p h y = s := same_content.symm
      have ux : IsUnit u.1 ∨ IsUnit u.2 := scaled_primitive x
      have vy : IsUnit v.1 ∨ IsUnit v.2 := by
        change IsUnit (scaledPair p h s y).1 ∨ IsUnit (scaledPair p h s y).2
        rw [← sy]
        exact scaled_primitive y
      have profile : ∀ k i : ℕ, i ≤ m →
          ((step^[k] (reducePair p (h - s) i u)).1 = 0 ↔
            (step^[k] (reducePair p (h - s) i v)).1 = 0) := by
        intro k i hi
        have left := normalized_zero x k i (hi.trans hm)
        have right := normalized_zero y k i (by simpa only [sy] using hi.trans hm)
        rw [sy] at right
        exact left.trans ((by rw [recover_depth _ _ (future k)] :
          (s + i ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
            ((step^[k] x).1.val : ℤ)) ↔
          (s + i ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
            ((step^[k] y).1.val : ℤ))).trans right.symm)
      have hits_same : (∃ k : ℕ, (step^[k] (reducePair p (h - s) m u)).1 = 0) ↔
          ∃ k : ℕ, (step^[k] (reducePair p (h - s) m v)).1 = 0 :=
        exists_congr fun k => profile k m le_rfl
      by_cases hit : ∃ k : ℕ, (step^[k] (reducePair p (h - s) m u)).1 = 0
      · have hit_v := hits_same.mp hit
        let t := Nat.find hit
        have same_t : Nat.find hit_v = t :=
          Nat.find_congr' (fun {k} => (profile k m le_rfl).symm)
        have ht : (step^[t] (reducePair p (h - s) m u)).1 = 0 := Nat.find_spec hit
        have phase (k : ℕ) :
            (step^[k] (reducePair p (h - s) m u)).1 = 0 ↔
              k % zeroRank (p ^ m) = t % zeroRank (p ^ m) := by
          let f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))
          exact primitive_hit_phase p m hp _
            (ux.imp (fun h => h.map f) (fun h => h.map f)) t k ht
        let r := zeroRank (p ^ m)
        have hr : 0 < r :=
          ((PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p 2 hp le_rfl).1 m).1
        have htr : (step^[t + r] (reducePair p (h - s) m u)).1 = 0 := by
          apply (phase _).mpr
          simp [r]
        have high_at (k : ℕ)
            (hk : (step^[k] (reducePair p (h - s) m u)).1 = 0) :
            e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
              ((step^[k] x).1.val : ℤ) ∧
            e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
              ((step^[k] y).1.val : ℤ) := by
          have hxk := (normalized_zero x k m hm).mp hk
          have hyhit : (step^[k] (reducePair p (h - content p h y) m
              (scaledPair p h (content p h y) y))).1 = 0 := by
            rw [sy]
            exact (profile k m le_rfl).mp hk
          have hyk := (normalized_zero y k m (by rw [sy]; exact hm)).mp hyhit
          change s + m ≤ _ at hxk
          rw [sy] at hyk
          have sem : s + m = e := Nat.add_sub_of_le lowx.le
          rw [sem] at hxk hyk
          exact ⟨hxk, hyk⟩
        have same_A : (step^[t] x).1 = (step^[t] y).1 :=
          (high_scalar _ _ (high_at t ht).1 (high_at t ht).2).mp (future t)
        have same_next : (step^[t + r] x).1 = (step^[t + r] y).1 :=
          (high_scalar _ _ (high_at _ htr).1 (high_at _ htr).2).mp (future _)
        have product : (Nat.fib r : ZMod (p ^ h)) *
            ((step^[t] x).2 - (step^[t] y).2) = 0 := by
          rw [Nat.add_comm t r, Function.iterate_add_apply, Function.iterate_add_apply] at same_next
          rw [first_readout r (step^[t] x), first_readout r (step^[t] y)] at same_next
          simp only [readout, same_A] at same_next
          linear_combination same_next
        have bx : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
            ((step^[t] x).2.val : ℤ) := by
          simpa only [Function.iterate_succ_apply', step] using base_depth x (t + 1)
        have by_ : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
            ((step^[t] y).2.val : ℤ) := by
          simpa only [Function.iterate_succ_apply', step, sy] using base_depth y (t + 1)
        have same_U : (ZMod.cast (scaledPair p h s (step^[t] x)).2 :
            ZMod (p ^ (h - s - padicValInt p (Nat.fib r : ℤ)))) =
            ZMod.cast (scaledPair p h s (step^[t] y)).2 := by
          rw [quotient_second _ _ _ (Nat.sub_le _ _) bx,
            quotient_second _ _ _ (Nat.sub_le _ _) by_]
          exact (hit_precision s r hr _ _ bx by_).mp product
        rw [low_label x s rfl high, low_label y s sy high,
          dif_pos hit, dif_pos hit_v]
        change LocalLabel.hit s t (step^[t] x).1 _ =
          LocalLabel.hit s (Nat.find hit_v) (step^[Nat.find hit_v] y).1 _
        rw [same_t, same_A]
        exact congrArg (LocalLabel.hit s t (step^[t] y).1) same_U
      · have no_v : ¬ ∃ k : ℕ, (step^[k] (reducePair p (h - s) m v)).1 = 0 :=
          fun hv => hit (hits_same.mpr hv)
        obtain ⟨j, hj, topx, topy, directions⟩ :=
          (primitive_no_hit_profile p (h - s) m hp hm u v ux vy hit no_v).mp profile
        have nyhigh : ¬ e ≤ content p h y := by simpa only [sy] using high
        have no_y : ¬ ∃ k : ℕ,
            (step^[k] (reducePair p (h - content p h y) (e - content p h y)
              (scaledPair p h (content p h y) y))).1 = 0 := by
          rw [sy]
          exact no_v
        unfold localLabel
        dsimp only
        rw [dif_neg high, dif_neg nyhigh, dif_neg hit, dif_neg no_y]
        rw [sy]
        change LocalLabel.noHit s (topHit p (h - s) m u)
          (if topHit p (h - s) m u = 0 then none else
            some (direction p (h - s) (topHit p (h - s) m u) u)) =
          LocalLabel.noHit s (topHit p (h - s) m v)
          (if topHit p (h - s) m v = 0 then none else
            some (direction p (h - s) (topHit p (h - s) m v) v))
        rw [topx, topy]
        split_ifs with hj0
        · rfl
        · rw [directions]
    · intro labels
      have same_content : content p h x = content p h y :=
        (label_content_eq x).symm.trans ((congrArg label_content labels).trans (label_content_eq y))
      have lowx : content p h x < e := Nat.lt_of_not_ge high
      let s := content p h x
      let m := e - s
      have hm : m ≤ h - s := Nat.sub_le_sub_right he s
      let u := scaledPair p h s x
      let v := scaledPair p h s y
      have sy : content p h y = s := same_content.symm
      have ux : IsUnit u.1 ∨ IsUnit u.2 := scaled_primitive x
      have vy : IsUnit v.1 ∨ IsUnit v.2 := by
        change IsUnit (scaledPair p h s y).1 ∨ IsUnit (scaledPair p h s y).2
        rw [← sy]
        exact scaled_primitive y
      have nyhigh : ¬ e ≤ content p h y := by rw [sy]; exact high
      rw [low_label x s rfl high, low_label y s sy high] at labels
      by_cases hit : ∃ k : ℕ, (step^[k] (reducePair p (h - s) m u)).1 = 0
      · by_cases hit_v : ∃ k : ℕ, (step^[k] (reducePair p (h - s) m v)).1 = 0
        · rw [dif_pos hit, dif_pos hit_v] at labels
          have same_t : Nat.find hit = Nat.find hit_v := by injection labels
          rw [← same_t] at labels
          let t := Nat.find hit
          have same_A : (step^[t] x).1 = (step^[t] y).1 := by injection labels
          have same_U : (ZMod.cast (scaledPair p h s (step^[t] x)).2 :
              ZMod (p ^ (h - s - padicValInt p (Nat.fib (zeroRank (p ^ m)) : ℤ)))) =
              ZMod.cast (scaledPair p h s (step^[t] y)).2 := by injection labels
          have ht : (step^[t] (reducePair p (h - s) m u)).1 = 0 := Nat.find_spec hit
          have htv : (step^[t] (reducePair p (h - s) m v)).1 = 0 := by
            change (step^[Nat.find hit] (reducePair p (h - s) m v)).1 = 0
            rw [same_t]
            exact Nat.find_spec hit_v
          let r := zeroRank (p ^ m)
          have hr : 0 < r :=
            ((PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon p 2 hp le_rfl).1 m).1
          have high_t_x : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
              ((step^[t] x).1.val : ℤ) := by
            have hz := (normalized_zero x t m hm).mp ht
            have sem : content p h x + m = e := Nat.add_sub_of_le lowx.le
            rwa [sem] at hz
          have high_t_y : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
              ((step^[t] y).1.val : ℤ) := by
            have hyhit : (step^[t] (reducePair p (h - content p h y) m
                (scaledPair p h (content p h y) y))).1 = 0 := by rw [sy]; exact htv
            have hz := (normalized_zero y t m (by rw [sy]; exact hm)).mp hyhit
            rw [sy] at hz
            have sem : s + m = e := Nat.add_sub_of_le lowx.le
            rwa [sem] at hz
          have profile (k i : ℕ) (hi : i ≤ m) :
              ((step^[k] (reducePair p (h - s) i u)).1 = 0 ↔
               (step^[k] (reducePair p (h - s) i v)).1 = 0) := by
            have hix : (step^[t] (reducePair p (h - s) i u)).1 = 0 :=
              (normalized_zero x t i (hi.trans hm)).mpr
                ((Nat.add_le_add_left hi s).trans
                  ((Nat.add_sub_of_le lowx.le) ▸ high_t_x))
            have hiy : (step^[t] (reducePair p (h - s) i v)).1 = 0 := by
              have hz := normalized_zero y t i (by rw [sy]; exact hi.trans hm)
              rw [sy] at hz
              exact hz.mpr ((Nat.add_le_add_left hi s).trans
                ((Nat.add_sub_of_le lowx.le) ▸ high_t_y))
            let f := ZMod.castHom (pow_dvd_pow p (hi.trans hm)) (ZMod (p ^ i))
            exact (primitive_hit_phase p i hp _
              (ux.imp (fun h => h.map f) (fun h => h.map f)) t k hix).trans
              (primitive_hit_phase p i hp _
                (vy.imp (fun h => h.map f) (fun h => h.map f)) t k hiy).symm
          have phase (k : ℕ) :
              (step^[k] (reducePair p (h - s) m u)).1 = 0 ↔ k % r = t % r := by
            let f := ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))
            exact primitive_hit_phase p m hp _
              (ux.imp (fun h => h.map f) (fun h => h.map f)) t k ht
          have tsmall : t < r := by
            have at_mod : (step^[t % r] (reducePair p (h - s) m u)).1 = 0 :=
              (phase _).mpr (Nat.mod_mod _ _)
            have minimal : t ≤ t % r := Nat.find_min' hit at_mod
            exact minimal.trans_lt (Nat.mod_lt _ hr)
          have bx : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
              ((step^[t] x).2.val : ℤ) := by
            simpa only [Function.iterate_succ_apply', step] using base_depth x (t + 1)
          have by_ : s ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
              ((step^[t] y).2.val : ℤ) := by
            simpa only [Function.iterate_succ_apply', step, sy] using base_depth y (t + 1)
          rw [quotient_second _ _ _ (Nat.sub_le _ _) bx,
            quotient_second _ _ _ (Nat.sub_le _ _) by_] at same_U
          have product : (Nat.fib r : ZMod (p ^ h)) *
              ((step^[t] x).2 - (step^[t] y).2) = 0 :=
            (hit_precision s r hr _ _ bx by_).mpr same_U
          let X := ((step^[t] x).2 - (step^[t] x).1, (step^[t] x).1)
          let Y := ((step^[t] y).2 - (step^[t] y).1, (step^[t] y).1)
          have first_sample : readout (p ^ h) 0 X = readout (p ^ h) 0 Y := by
            simpa only [readout, Nat.fib_zero, Nat.fib_one, Nat.cast_zero, Nat.cast_one,
              zero_mul, one_mul, zero_add] using same_A
          have second_sample : readout (p ^ h) r X = readout (p ^ h) r Y := by
            dsimp only [X, Y, readout]
            rw [same_A]
            linear_combination product
          let times : Fin 2 → ℕ := ![0, r]
          have increasing : StrictMono times := by
            intro a b hab
            fin_cases a <;> fin_cases b
            · exact (lt_irrefl _ hab).elim
            · exact hr
            · exact (show ¬ (1 : Fin 2) < 0 by decide) hab |>.elim
            · exact (lt_irrefl _ hab).elim
          have finite_samples : (fun i => readout (p ^ h) (times i) X) =
              (fun i => readout (p ^ h) (times i) Y) := by
            funext i
            fin_cases i
            · exact first_sample
            · exact second_sample
          have coarse : ∀ j : ℕ, readout (p ^ h) (j * r) X =
              readout (p ^ h) (j * r) Y := by
            have hf := (SamplingQuotient.sampling_quotient (p ^ h) 2
              (pow_pos hp.pos h) le_rfl times increasing).2.2.1 X Y
            simpa [times, Finset.univ_fin2] using hf.mp finite_samples
          intro k
          by_cases hk : (step^[k] (reducePair p (h - s) m u)).1 = 0
          · have high_k_x : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
                ((step^[k] x).1.val : ℤ) := by
              have hz := (normalized_zero x k m hm).mp hk
              have sem : content p h x + m = e := Nat.add_sub_of_le lowx.le
              rwa [sem] at hz
            have high_k_y : e ≤ D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
                ((step^[k] y).1.val : ℤ) := by
              have hyhit : (step^[k] (reducePair p (h - content p h y) m
                  (scaledPair p h (content p h y) y))).1 = 0 := by
                rw [sy]; exact (profile k m le_rfl).mp hk
              have hz := (normalized_zero y k m (by rw [sy]; exact hm)).mp hyhit
              rw [sy] at hz
              have sem : s + m = e := Nat.add_sub_of_le lowx.le
              rwa [sem] at hz
            have modk : k % r = t := by
              simpa only [Nat.mod_eq_of_lt tsmall] using (phase k).mp hk
            have grid : k = t + (k / r) * r := by
              have hg := Nat.mod_add_div k r
              rw [modk, Nat.mul_comm r] at hg
              exact hg.symm
            apply (high_scalar _ _ high_k_x high_k_y).mpr
            rw [grid, Nat.add_comm t, Function.iterate_add_apply, Function.iterate_add_apply,
              first_readout ((k / r) * r) (step^[t] x),
              first_readout ((k / r) * r) (step^[t] y)]
            exact coarse (k / r)
          · have low : D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
                ((step^[k] x).1.val : ℤ) < e := by
              have threshold := normalized_zero x k m hm
              have sem : content p h x + m = e := Nat.add_sub_of_le lowx.le
              rw [sem] at threshold
              exact Nat.lt_of_not_ge (fun he => hk (threshold.mpr he))
            apply low_profile x y same_content (fun k i hi => ?_) k low
            rw [sy]
            exact profile k i hi
        · rw [dif_pos hit, dif_neg hit_v] at labels
          cases labels
      · by_cases hit_v : ∃ k : ℕ, (step^[k] (reducePair p (h - s) m v)).1 = 0
        · rw [dif_neg hit, dif_pos hit_v] at labels
          cases labels
        · rw [dif_neg hit, dif_neg hit_v] at labels
          have same_j : topHit p (h - s) m u = topHit p (h - s) m v := by injection labels
          obtain ⟨j, hj, tx, _, _⟩ :=
            (primitive_no_hit_profile p (h - s) m hp hm u u ux ux hit hit).mp
              (fun _ _ _ => Iff.rfl)
          have ty : topHit p (h - s) m v = j := same_j.symm.trans tx
          rw [tx, ty] at labels
          have directions : direction p (h - s) j u = direction p (h - s) j v := by
            by_cases hj0 : j = 0
            · rw [hj0]
              let : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
              exact congrArg (MulAction.orbit (ZMod (p ^ 0))ˣ) (Subsingleton.elim _ _)
            · simp only [if_neg hj0] at labels
              have hd : some (direction p (h - s) j u) = some (direction p (h - s) j v) := by
                injection labels
              exact Option.some.inj hd
          have profile := (primitive_no_hit_profile p (h - s) m hp hm u v ux vy hit hit_v).mpr
            ⟨j, hj, tx, ty, directions⟩
          intro k
          have low : D5.S3.Arith.Congruence.PrimePowerAffineBehavior.depth p h
              ((step^[k] x).1.val : ℤ) < e := by
            have nz : ¬ (step^[k] (reducePair p (h - s) m u)).1 = 0 := fun hk => hit ⟨k, hk⟩
            have threshold := normalized_zero x k m hm
            have sem : content p h x + m = e := Nat.add_sub_of_le lowx.le
            rw [sem] at threshold
            exact Nat.lt_of_not_ge (fun hk => nz (threshold.mpr hk))
          apply low_profile x y same_content (fun k i hi => ?_) k low
          rw [sy]
          exact profile k i hi

#print axioms result

end D5.S3.Arith.FibonacciAtomic.GraftLocalBehaviorLabels
