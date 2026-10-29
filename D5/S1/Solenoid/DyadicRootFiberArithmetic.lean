/- GID: D5/S1/Solenoid/DyadicRootFiberArithmetic
   generality: I
   mirror-B: D5/B/S1/Solenoid/DyadicRootFiberArithmetic
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: The odd part of a degree classifies the cyclic kernel and every root fiber in the dyadic solenoid. -/

import D5.S1.Solenoid.DyadicTimeSeparation
import Mathlib.GroupTheory.Coset.Basic

noncomputable section

namespace D5.S1.Solenoid.DyadicSolenoid

private theorem strip_twos (k : ℕ) (x : DyadicSolenoid)
    (hx : (2 ^ k : ℕ) • x = 0) : x = 0 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    apply dyadic_time_separation.2.2.2.2.2.1
    simpa only [pow_succ, mul_comm, mul_smul] using hx

private theorem torsion_coordinates (q s : ℕ) (hs : 2 * s = q + 1)
    (x : DyadicSolenoid) (hx : q • x = 0) (n : ℕ) :
    x.1 n = (s ^ n : ℕ) • x.1 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : q • x.1 (n + 1) = 0 :=
      congrArg (fun y : DyadicSolenoid => y.1 (n + 1)) hx
    calc
      x.1 (n + 1) = (q + 1) • x.1 (n + 1) := by rw [add_nsmul, ht]; simp
      _ = s • (2 • x.1 (n + 1)) := by rw [← mul_smul, mul_comm, hs]
      _ = s • x.1 n := by rw [x.2 n]
      _ = (s ^ (n + 1) : ℕ) • x.1 0 := by rw [ih, pow_succ, mul_comm, mul_smul]

/-- For a degree with odd part `q`, the multiplication kernel is cyclic of order `q`,
and every root fiber has exactly `q` elements. The carrier retains its product topology. -/
theorem dyadic_root_fiber_arithmetic (k q : ℕ) (hq : Odd q) :
    Nonempty ((nsmulAddHom (2 ^ k * q) DyadicSolenoid).ker ≃+ ZMod q) ∧
    ∀ a : DyadicSolenoid,
      Finite {x : DyadicSolenoid // (2 ^ k * q) • x = a} ∧
      Nat.card {x : DyadicSolenoid // (2 ^ k * q) • x = a} = q := by
  obtain ⟨d, hd⟩ := hq
  have hpos : 0 < q := by omega
  letI : NeZero q := ⟨by omega⟩
  let s := d + 1
  have hs : 2 * s = q + 1 := by dsimp [s]; omega
  have ht (z : ZMod q) : q • ZMod.toAddCircle z = 0 := by
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  let lift : ZMod q →+ DyadicSolenoid :=
    { toFun := fun z => ⟨fun n => (s ^ n : ℕ) • ZMod.toAddCircle z, by
        intro n
        rw [pow_succ, ← mul_smul, ← mul_assoc, mul_comm (s ^ n) s,
          mul_assoc, hs, mul_smul, add_nsmul, ht]
        simp⟩
      map_zero' := by ext n; simp
      map_add' := by intro z w; ext n; simp [nsmul_add] }
  let f : ZMod q →+ (nsmulAddHom (2 ^ k * q) DyadicSolenoid).ker :=
    { toFun := fun z => ⟨lift z, by
        change (2 ^ k * q) • lift z = 0
        rw [mul_smul]
        have hz : q • lift z = 0 := by
          ext n
          change q • ((s ^ n : ℕ) • ZMod.toAddCircle z) = 0
          rw [smul_comm, ht, smul_zero]
        rw [hz, smul_zero]⟩
      map_zero' := by apply Subtype.ext; exact lift.map_zero
      map_add' := by intro z w; apply Subtype.ext; exact lift.map_add z w }
  have hinj : Function.Injective f := by
    intro z w he
    apply ZMod.toAddCircle_injective
    have he0 := congrArg (fun y : (nsmulAddHom (2 ^ k * q) DyadicSolenoid).ker =>
      y.1.1 0) he
    simpa [f, lift] using he0
  have hsurj : Function.Surjective f := by
    intro x
    have hx : q • x.1 = 0 := by
      apply strip_twos k
      simpa only [← mul_smul] using x.2
    have hx0 : q • x.1.1 0 = 0 := congrArg (fun y : DyadicSolenoid => y.1 0) hx
    obtain ⟨r, _, hr⟩ := (AddCircle.nsmul_eq_zero_iff hpos).mp hx0
    refine ⟨(r : ZMod q), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext n
    change (s ^ n : ℕ) • ZMod.toAddCircle (r : ZMod q) = x.1.1 n
    rw [torsion_coordinates q s hs x.1 hx n]
    congr 1
    simpa using (ZMod.toAddCircle_natCast q r).trans hr
  let e := (AddEquiv.ofBijective f ⟨hinj, hsurj⟩).symm
  refine ⟨⟨e⟩, ?_⟩
  intro a
  have hm : 0 < 2 ^ k * q := Nat.mul_pos (by positivity) hpos
  let t := (nsmulAddHom (2 ^ k * q) DyadicSolenoid).fiberEquivKerOfSurjective
    (dyadic_time_separation.2.2.2.2.1 _ hm) a
  let eqv := t.trans e.toEquiv
  haveI : Finite {x : DyadicSolenoid // (2 ^ k * q) • x = a} :=
    Finite.of_equiv (ZMod q) eqv.symm
  exact ⟨inferInstance, (Nat.card_congr eqv).trans (ZMod.natCard q)⟩

end D5.S1.Solenoid.DyadicSolenoid
