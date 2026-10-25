/- GID: D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim; result=D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result; claim=D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim
   digest: Jacobi and reducedness obstruct the proposed E6 and truck spinor Poisson brackets. -/

import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic

/-! The diagonal spinor brackets force their weight element to vanish in a reduced algebra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation

/-- A complex bilinear, antisymmetric biderivation satisfying the Jacobi identity. -/
def IsPoissonBracket {R : Type*} [CommRing R] [Algebra ℂ R] (br : R → R → R) : Prop :=
  (∀ a b c, br (a + b) c = br a c + br b c) ∧
  (∀ (c : ℂ) a b, br (c • a) b = c • br a b) ∧
  (∀ a b c, br a (b + c) = br a b + br a c) ∧
  (∀ (c : ℂ) a b, br a (c • b) = c • br a b) ∧
  (∀ a b, br a b = -br b a) ∧
  (∀ a b c, br a (b * c) = br a b * c + b * br a c) ∧
  (∀ a b c, br a (br b c) + br b (br c a) + br c (br a b) = 0)

/-- Uniform diagonal mixed spinor brackets, weights, and vanishing equal-charge brackets. -/
def SpinorBrackets {R : Type*} [CommRing R] {N : ℕ}
    (br : R → R → R) (h : R) (sUp sDn : Fin N → R) (e : ℕ) : Prop :=
  (∀ α, br h (sUp α) = sUp α) ∧
  (∀ α, br h (sDn α) = -sDn α) ∧
  (∀ α β, br (sUp α) (sDn β) = if α = β then h ^ e else 0) ∧
  (∀ α β, br (sUp α) (sUp β) = 0) ∧
  (∀ α β, br (sDn α) (sDn β) = 0)

/-- The proposed brackets for every admissible member of the second E6 family. -/
def ConjE6 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ (R : Type) (ringR : CommRing R),
    letI := ringR
    ∃ algR : Algebra ℂ R,
      letI := algR
      IsReduced R ∧ ∃ (br : R → R → R) (h : R) (sUp sDn : Fin (2 ^ (2 * n)) → R),
        IsPoissonBracket br ∧ h ≠ 0 ∧ SpinorBrackets br h sUp sDn (n - 1)

/-- The proposed brackets for every admissible truck rank and positive multiplicity. -/
def ConjTruck : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ σ : ℕ, 1 ≤ σ → ∃ (R : Type) (ringR : CommRing R),
    letI := ringR
    ∃ algR : Algebra ℂ R,
      letI := algR
      IsReduced R ∧ ∃ (br : R → R → R) (h : R) (sUp sDn : Fin (2 ^ (2 * n)) → R),
        IsPoissonBracket br ∧ h ≠ 0 ∧ SpinorBrackets br h sUp sDn (n + σ - 1)

/-- At least one of the two proposed families exists in reduced complex algebras. -/
def claim : Prop := ConjE6 ∨ ConjTruck

private def hamiltonian {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a : R) : Derivation ℂ R R := by
  refine Derivation.mk' {
    toFun := br a
    map_add' := hp.2.2.1 a
    map_smul' := fun c b => hp.2.2.2.1 c a b } ?_
  intro b c
  change br a (b * c) = b • br a c + c • br a b
  rw [hp.2.2.2.2.2.1]
  simp only [smul_eq_mul]
  ring

private lemma bracket_pow {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a h : R) (k : ℕ) :
    br a (h ^ k) = k • (h ^ (k - 1) * br a h) := by
  have hk := (hamiltonian br hp a).leibniz_pow h k
  unfold hamiltonian at hk
  simpa only [Derivation.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul, nsmul_eq_mul, mul_assoc] using hk

private lemma bracket_mul_left {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a b c : R) :
    br (a * b) c = a * br b c + br a c * b := by
  have ha := hp.2.2.2.2.1
  rw [ha (a * b) c, hp.2.2.2.2.2.1, ha c a, ha c b]
  ring

private lemma bracket_forces_zero {R : Type*} [CommRing R] [Algebra ℂ R] [IsReduced R]
    (br : R → R → R) (hp : IsPoissonBracket br) (e : ℕ) (he : 1 ≤ e)
    (h x y z w : R) (hhx : br h x = x) (hhy : br h y = -y)
    (hxy : br x y = h ^ e) (hzw : br z w = h ^ e)
    (hxw : br x w = 0) (hxz : br x z = 0) : h = 0 := by
  have ha := hp.2.2.2.2.1
  have hz (a : R) : br a 0 = 0 := by
    have hh := (hamiltonian br hp a).map_zero
    unfold hamiltonian at hh
    simpa only [Derivation.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using hh
  cases e with
  | zero => exact (Nat.not_succ_le_zero 0 he).elim
  | succ k =>
    have hwx : br w x = 0 := by rw [ha w x, hxw, neg_zero]
    have hxh : br x h = -x := by rw [ha x h, hhx]
    have hj := hp.2.2.2.2.2.2 x z w
    rw [hzw, hwx, hxz, hz z, hz w, add_zero, add_zero,
      bracket_pow br hp x h (k + 1), hxh] at hj
    have hpowx : h ^ k * x = 0 := by
      have hc : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have hscaled : ((k + 1 : ℕ) : ℂ) • (h ^ k * x) = 0 := by
        rw [Nat.cast_smul_eq_nsmul]
        simpa only [Nat.add_sub_cancel, mul_neg, smul_neg, neg_eq_zero] using hj
      have hh := congrArg (fun a : R => ((k + 1 : ℕ) : ℂ)⁻¹ • a) hscaled
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] using hh
    have hzero : br (h ^ k * x) y = 0 := by
      rw [hpowx, ha 0 y, hz y, neg_zero]
    rw [bracket_mul_left br hp, hxy, ha (h ^ k) y,
      bracket_pow br hp y h k, ha y h, hhy, neg_neg] at hzero
    simp only [nsmul_eq_mul] at hzero
    have hterm : h * ((k : R) * (h ^ (k - 1) * y)) * x = 0 := by
      cases k with
      | zero => simp only [Nat.cast_zero, zero_mul, mul_zero]
      | succ m =>
        calc
          h * ((↑(m + 1) : R) * (h ^ (m + 1 - 1) * y)) * x =
              (↑(m + 1) : R) * (h ^ (m + 1) * x) * y := by
                simp only [Nat.add_sub_cancel, pow_succ]
                ring
          _ = 0 := by rw [hpowx, mul_zero, zero_mul]
    have hnil : h ^ (2 * (k + 1)) = 0 := by
      calc
        h ^ (2 * (k + 1)) = h * (h ^ k * h ^ (k + 1)) := by
          rw [Nat.mul_comm, pow_mul, pow_two, pow_succ]
          ring
        _ = h * (h ^ k * h ^ (k + 1) + -((k : R) * (h ^ (k - 1) * y)) * x) +
              h * ((k : R) * (h ^ (k - 1) * y)) * x := by ring
        _ = 0 := by rw [hzero, hterm, mul_zero, add_zero]
    exact (show IsNilpotent h from ⟨2 * (k + 1), hnil⟩).eq_zero

private lemma spinor_forces_zero {R : Type*} [CommRing R] [Algebra ℂ R] [IsReduced R]
    {N : ℕ} (hN : 2 ≤ N) (br : R → R → R) (hp : IsPoissonBracket br)
    (h : R) (sUp sDn : Fin N → R) (e : ℕ) (he : 1 ≤ e)
    (hs : SpinorBrackets br h sUp sDn e) : h = 0 := by
  let i : Fin N := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hN⟩
  let j : Fin N := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hN⟩
  have hij : i ≠ j := by
    intro hij
    have := congrArg Fin.val hij
    change 0 = 1 at this
    exact Nat.zero_ne_one this
  apply bracket_forces_zero br hp e he h (sUp i) (sDn i) (sUp j) (sDn j)
  · exact hs.1 i
  · exact hs.2.1 i
  · rw [hs.2.2.1, ite_eq_left rfl]
  · rw [hs.2.2.1, ite_eq_left rfl]
  · rw [hs.2.2.1, ite_eq_right hij]
  · exact hs.2.2.2.1 i j

private lemma not_conjE6 : ¬ ConjE6 := by
  intro hc
  obtain ⟨R, ringR, algR, hr, br, h, sUp, sDn, hp, hn, hs⟩ := hc 3 (by decide)
  let _ := ringR
  let _ := algR
  let _ := hr
  exact hn (spinor_forces_zero (by decide) br hp h sUp sDn 2 (by decide) hs)

private lemma not_conjTruck : ¬ ConjTruck := by
  intro hc
  obtain ⟨R, ringR, algR, hr, br, h, sUp, sDn, hp, hn, hs⟩ :=
    hc 2 (by decide) 1 (by decide)
  let _ := ringR
  let _ := algR
  let _ := hr
  exact hn (spinor_forces_zero (by decide) br hp h sUp sDn 2 (by decide) hs)

/-- Neither proposed family of spinor brackets exists in reduced complex algebras. -/
theorem result : ¬ claim := by
  intro hc
  rcases hc with hc | hc
  · exact not_conjE6 hc
  · exact not_conjTruck hc

end D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation

#print axioms D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.result

open Lean in
run_cmd do
  let env ← getEnv
  let moduleName := "D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation"
  let roots := [``D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.result,
    ``D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation.claim]
  let mut pending := roots
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless visited.contains name do
      visited := visited.insert name
      if let some info := env.find? name then
        pending := info.type.getUsedConstants.toList ++ pending
        if let some value := info.value? (allowOpaque := true) then
          pending := value.getUsedConstants.toList ++ pending
  let entries := env.constants.toList.filter fun entry =>
    (entry.1.toString.splitOn moduleName).length > 1
  let rows := entries.map fun (name, info) =>
    let dependencies := info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
    Json.mkObj [
      ("name", toJson name.toString),
      ("user_name", toJson (privateToUserName name).toString),
      ("private", toJson (isPrivateName name)),
      ("reachable", toJson (visited.contains name)),
      ("direct_dependencies", toJson (dependencies.map Name.toString))]
  let unreachable := entries.filter fun (name, _) => !visited.contains name
  let some claimInfo := env.find? roots[1]! | throwError "claim missing"
  let some resultInfo := env.find? roots[0]! | throwError "result missing"
  let literalProp := claimInfo.type == Expr.sort Level.zero
  let literalNotClaim := resultInfo.type == mkApp (mkConst ``Not) (mkConst roots[1]!)
  let report := Json.mkObj [
    ("roots", toJson (roots.map Name.toString)),
    ("constant_count", toJson entries.length),
    ("closure_size", toJson visited.toArray.size),
    ("unreachable", toJson (unreachable.map fun row => row.1.toString)),
    ("claim_literal_Prop", toJson literalProp),
    ("result_literal_Not_claim", toJson literalNotClaim),
    ("constants", Json.arr rows.toArray)]
  IO.FS.writeFile "/Users/chronoai/.sshx/4c3fd99787b7d7541a2bf8a8/attempt-1/closure-audit.json"
    (report.pretty ++ "\n")
  IO.FS.writeFile "/Users/chronoai/.sshx/4c3fd99787b7d7541a2bf8a8/attempt-1/namespace-constants.txt"
    (String.intercalate "\n" (entries.map fun row => row.1.toString) ++ "\n")
  logInfo m!"CLOSURE_AUDIT constants={entries.length} unreachable={unreachable.length}"
  logInfo m!"COMPILED_SHAPE claim:Prop={literalProp} result:Not_claim={literalNotClaim}"
  unless unreachable.isEmpty && literalProp && literalNotClaim do
    throwError "closure or utility shape audit failed"

namespace D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation

example : Nonempty ℂ := ⟨0⟩

example : (0 : ℂ) = 0 := by
  have hp : IsPoissonBracket (R := ℂ) (fun _ _ => 0) := by
    unfold IsPoissonBracket
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp
  exact bracket_forces_zero (fun _ _ => 0) hp 1 (by decide) 0 0 0 0 0
    (by simp) (by simp) (by simp) (by simp) rfl rfl

end D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation
