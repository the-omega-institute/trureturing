/- GID: D5/S1/Solenoid/ExactSequence
   generality: I
   mirror-B: D5/B/S1/Solenoid/ExactSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible congruence data form exactly the kernel of the solenoid phase projection. -/

import D5.S1.Dynamics.UniversalSolenoid
import Mathlib.Algebra.Exact.Basic

/- Provenance: the pinned library supplies `Function.Exact`, the canonical
   `ZMod.toAddCircle` embedding, its injectivity, and
   `AddCircle.nsmul_eq_zero_iff`. It has no solenoid or profinite-kernel
   classification, so the compatible-coordinate construction is proved here. -/

namespace D5.S1.Solenoid.ExactSequence

open Function
open D5.S1.Dynamics

/-- One residue at every positive modulus, compatible under divisibility. -/
abbrev CongruenceData :=
  {x : (m : ℕ+) → ZMod m.1 //
    ∀ m n : ℕ+,
      ZMod.castHom (show m.1 ∣ m.1 * n.1 from dvd_mul_right m.1 n.1)
          (ZMod m.1) (x ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩) = x m}

instance : Zero CongruenceData :=
  ⟨⟨fun _ => 0, by intro m n; simp⟩⟩

instance : Add CongruenceData :=
  ⟨fun x y => ⟨x.1 + y.1, by
    intro m n
    change (ZMod.castHom (show m.1 ∣ m.1 * n.1 from dvd_mul_right m.1 n.1)
      (ZMod m.1) (x.1 ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ +
        y.1 ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩)) = x.1 m + y.1 m
    rw [map_add, x.2 m n, y.2 m n]⟩⟩

instance : Neg CongruenceData :=
  ⟨fun x => ⟨-x.1, by
    intro m n
    change (ZMod.castHom (show m.1 ∣ m.1 * n.1 from dvd_mul_right m.1 n.1)
      (ZMod m.1) (-x.1 ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩)) = -x.1 m
    rw [map_neg, x.2 m n]⟩⟩

instance : AddCommGroup CongruenceData where
  add := (· + ·)
  add_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  zero := 0
  zero_add _ := Subtype.ext (zero_add _)
  add_zero _ := Subtype.ext (add_zero _)
  neg := Neg.neg
  neg_add_cancel _ := Subtype.ext (neg_add_cancel _)
  add_comm _ _ := Subtype.ext (add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

private noncomputable def residueCircle (m : ℕ+) :
    ZMod m.1 →+ UnitAddCircle := by
  letI : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact ZMod.toAddCircle

private theorem residueCircle_injective (m : ℕ+) :
    Injective (residueCircle m) := by
  letI : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact ZMod.toAddCircle_injective m.1

private theorem residueCircle_intCast (m : ℕ+) (k : ℤ) :
    residueCircle m (k : ZMod m.1) =
      (((k : ℝ) / m.1 : ℝ) : UnitAddCircle) := by
  letI : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact ZMod.toAddCircle_intCast k

private theorem residueCircle_natCast (m : ℕ+) (k : ℕ) :
    residueCircle m (k : ZMod m.1) =
      (((k : ℝ) / m.1 : ℝ) : UnitAddCircle) := by
  letI : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  exact ZMod.toAddCircle_natCast k

private theorem residueCircle_cast_mul (m n : ℕ+) (z : ZMod (m.1 * n.1)) :
    n.1 • residueCircle ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ z =
      residueCircle m
        (ZMod.castHom (show m.1 ∣ m.1 * n.1 from dvd_mul_right m.1 n.1)
          (ZMod m.1) z) := by
  letI : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
  letI : NeZero (m.1 * n.1) :=
    ⟨mul_ne_zero (Nat.ne_of_gt m.2) (Nat.ne_of_gt n.2)⟩
  rcases ZMod.intCast_surjective z with ⟨a, rfl⟩
  rw [ZMod.castHom_apply,
    ZMod.cast_intCast (R := ZMod m.1) (dvd_mul_right m.1 n.1) a]
  calc
    n.1 • residueCircle ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ (a : ZMod (m.1 * n.1)) =
        n.1 • (((a : ℝ) / (m.1 * n.1) : ℝ) : UnitAddCircle) := by
          simpa only [Nat.cast_mul] using
            congrArg (fun u : UnitAddCircle => n.1 • u)
              (residueCircle_intCast ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ a)
    _ = (((a : ℝ) / m.1 : ℝ) : UnitAddCircle) := by
          change n.1 • (((a : ℝ) / ((m.1 : ℝ) * n.1) : ℝ) : UnitAddCircle) = _
          rw [← AddCircle.coe_nsmul]
          apply congrArg (fun t : ℝ => (t : UnitAddCircle))
          rw [nsmul_eq_mul]
          push_cast
          field_simp [Nat.ne_of_gt m.2, Nat.ne_of_gt n.2]
    _ = residueCircle m (a : ZMod m.1) := by
          symm
          exact residueCircle_intCast m a

/-- Compatible residue coordinates define a pure-congruence solenoid element. -/
noncomputable def congruenceEmbedding : CongruenceData →+ UniversalSolenoid where
  toFun x := ⟨fun m => residueCircle m (x.1 m), by
    intro m n
    rw [residueCircle_cast_mul]
    exact congrArg (residueCircle m) (x.2 m n)⟩
  map_zero' := by
    apply Subtype.ext
    funext m
    exact map_zero (residueCircle m)
  map_add' x y := by
    apply Subtype.ext
    funext m
    exact map_add (residueCircle m) _ _

theorem congruence_embedding_injective : Injective congruenceEmbedding := by
  intro x y hxy
  apply Subtype.ext
  funext m
  apply residueCircle_injective m
  exact congrFun (congrArg Subtype.val hxy) m

private theorem coordinate_torsion
    (theta : UniversalSolenoid) (htheta : UniversalSolenoid.projection theta = 0)
    (m : ℕ+) : m.1 • theta.1 m = 0 := by
  calc
    m.1 • theta.1 m = theta.1 ⟨1, Nat.zero_lt_one⟩ := by
      have h := theta.2 ⟨1, Nat.zero_lt_one⟩ m
      have hm : (⟨1 * m.1, Nat.mul_pos Nat.zero_lt_one m.2⟩ : ℕ+) = m := by
        apply Subtype.ext
        simp
      rw [hm] at h
      exact h
    _ = UniversalSolenoid.projection theta := rfl
    _ = 0 := htheta

theorem congruence_embedding_exact_projection :
    Function.Exact congruenceEmbedding UniversalSolenoid.projection := by
  intro theta
  constructor
  · intro htheta
    have hexists (m : ℕ+) :
        ∃ k < m.1, (((k : ℝ) / m.1 : ℝ) : UnitAddCircle) = theta.1 m :=
      by simpa using
        (AddCircle.nsmul_eq_zero_iff m.2).mp (coordinate_torsion theta htheta m)
    choose k hk hcoordinate using hexists
    let x : CongruenceData := ⟨fun m => (k m : ZMod m.1), by
      intro m n
      apply residueCircle_injective m
      dsimp only
      rw [← residueCircle_cast_mul,
        residueCircle_natCast ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ (k ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩),
        residueCircle_natCast m (k m)]
      rw [hcoordinate ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩, theta.2 m n]
      exact (hcoordinate m).symm⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext m
    change residueCircle m (k m : ZMod m.1) = theta.1 m
    letI : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
    change ZMod.toAddCircle (k m : ZMod m.1) = theta.1 m
    rw [ZMod.toAddCircle_natCast]
    exact hcoordinate m
  · rintro ⟨x, rfl⟩
    change residueCircle ⟨1, Nat.zero_lt_one⟩
      (x.1 ⟨1, Nat.zero_lt_one⟩) = 0
    rw [show x.1 ⟨1, Nat.zero_lt_one⟩ = 0 from Subsingleton.elim _ _]
    exact map_zero _

/-- The congruence inclusion, visible phase projection, and their endpoint
maps form the element-level short exact sequence: compatible residue data are
exactly the invisible kernel, the inclusion is injective, and every visible
phase has a solenoid lift. -/
theorem congruence_solenoid_short_exact :
    Injective congruenceEmbedding ∧
      Function.Exact congruenceEmbedding UniversalSolenoid.projection ∧
      Surjective UniversalSolenoid.projection :=
  ⟨congruence_embedding_injective, congruence_embedding_exact_projection,
    UniversalSolenoid.projection_surjective⟩

end D5.S1.Solenoid.ExactSequence
