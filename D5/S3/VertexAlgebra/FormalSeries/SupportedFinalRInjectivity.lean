/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedFinalRInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Injectivity of the concrete final multiplier on genuinely nested-supported channels. -/
import D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
import D5.S3.VertexAlgebra.FormalSeries.SupportedChannelSeries

/-!
proof_shape: content
admission_basis: escape-witness
escape_witness: triple_zero proves vanishing by strong induction across x rows.
The prior x row vanishes inductively, reducing the current triple recurrence
to y+z; only that row's y cutoff licenses supported_positive_reconstruction.
The bivariate supplier does not supply this coupled cross-row inference.

Only the concrete x,y,x+y,x+y+z,y+z,z factors are cancelled. The triple
factor uses induction on the supported x row, followed by the existing
supported positive inverse in y. No z bound or uniform bound over x states
is required. Finite powers preserve the stated nested support.
-/
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.SupportedFinalRInjectivity
open UniformGradedLocalCorrelator SupportedChannelSeries
open scoped BigOperators
noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Exactly the support needed here, rather than a Laurent-series class.
The second cutoff may depend arbitrarily on the fixed first exponent. -/
def NestedSupport (F : Distribution 3 R) : Prop :=
  (∃ U : ℕ, ∀ x y z : ℤ, x < -(U : ℤ) → F ![x, y, z] = 0) ∧
    ∀ x : ℤ, ∃ B : ℕ, ∀ y z : ℤ, y < -(B : ℤ) → F ![x, y, z] = 0

private theorem variable_action (F : Distribution 3 R) (i : Fin 3) (e : Exponent 3) :
    polynomialAction (variablePolynomial i) F e = F (e - Pi.single i 1) := by
  rw [variablePolynomial, polynomialAction, AddMonoidAlgebra.lift_single]
  change (1 : ℂ) • F (e - Pi.single i 1) = _
  exact one_smul ℂ _

private theorem variable_xyz (F : Distribution 3 R) (i : Fin 3) (x y z : ℤ) :
    polynomialAction (variablePolynomial i) F ![x, y, z] =
      F ![x - (if i = 0 then 1 else 0), y - (if i = 1 then 1 else 0),
        z - (if i = 2 then 1 else 0)] := by
  rw [variable_action]
  congr 1
  funext c
  fin_cases i <;> fin_cases c <;> simp

private theorem xy_action (F : Distribution 3 R) (x y z : ℤ) :
    polynomialAction (variablePolynomial 0 + variablePolynomial 1) F ![x, y, z] =
      F ![x - 1, y, z] + F ![x, y - 1, z] := by
  simp [map_add, LinearMap.add_apply, variable_xyz]

private theorem yz_action (F : Distribution 3 R) (x y z : ℤ) :
    polynomialAction (variablePolynomial 1 + variablePolynomial 2) F ![x, y, z] =
      F ![x, y - 1, z] + F ![x, y, z - 1] := by
  simp [map_add, LinearMap.add_apply, variable_xyz]

private theorem triple_action (F : Distribution 3 R) (x y z : ℤ) :
    polynomialAction (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2)
      F ![x, y, z] =
        F ![x - 1, y, z] + F ![x, y - 1, z] + F ![x, y, z - 1] := by
  simp [map_add, LinearMap.add_apply, variable_xyz]

omit [Algebra ℂ R] in
private theorem nested_add (F G : Distribution 3 R)
    (hF : NestedSupport F) (hG : NestedSupport G) : NestedSupport (F + G) := by
  obtain ⟨⟨U, hu⟩, hf⟩ := hF
  obtain ⟨⟨V, hv⟩, hg⟩ := hG
  constructor
  · refine ⟨max U V, ?_⟩
    intro x y z hx
    change F ![x, y, z] + G ![x, y, z] = 0
    rw [hu x y z (by omega), hv x y z (by omega), add_zero]
  · intro x
    obtain ⟨B, hb⟩ := hf x
    obtain ⟨C, hc⟩ := hg x
    refine ⟨max B C, ?_⟩
    intro y z hy
    change F ![x, y, z] + G ![x, y, z] = 0
    rw [hb y z (by omega), hc y z (by omega), add_zero]

omit [Algebra ℂ R] in
private theorem nested_sub (F G : Distribution 3 R)
    (hF : NestedSupport F) (hG : NestedSupport G) : NestedSupport (F - G) := by
  obtain ⟨⟨U, hu⟩, hf⟩ := hF
  obtain ⟨⟨V, hv⟩, hg⟩ := hG
  constructor
  · refine ⟨max U V, ?_⟩
    intro x y z hx
    change F ![x, y, z] - G ![x, y, z] = 0
    rw [hu x y z (by omega), hv x y z (by omega), sub_self]
  · intro x
    obtain ⟨B, hb⟩ := hf x
    obtain ⟨C, hc⟩ := hg x
    refine ⟨max B C, ?_⟩
    intro y z hy
    change F ![x, y, z] - G ![x, y, z] = 0
    rw [hb y z (by omega), hc y z (by omega), sub_self]

private theorem variable_preserves (i : Fin 3) (F : Distribution 3 R)
    (hF : NestedSupport F) : NestedSupport (polynomialAction (variablePolynomial i) F) := by
  obtain ⟨⟨U, hu⟩, rows⟩ := hF
  constructor
  · refine ⟨U, ?_⟩
    intro x y z hx
    rw [variable_xyz]
    apply hu
    split_ifs <;> omega
  · intro x
    obtain ⟨B, hb⟩ := rows (x - (if i = 0 then 1 else 0))
    refine ⟨B, ?_⟩
    intro y z hy
    rw [variable_xyz]
    apply hb
    split_ifs <;> omega

private theorem power_preserves (q : LaurentPolynomial 3)
    (closed : ∀ F : Distribution 3 R, NestedSupport F → NestedSupport (polynomialAction q F))
    (n : ℕ) (F : Distribution 3 R) (hF : NestedSupport F) :
    NestedSupport (polynomialAction (q ^ n) F) := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [pow_succ', map_mul, Module.End.mul_apply]
    exact closed _ ih

private theorem power_zero (q : LaurentPolynomial 3)
    (closed : ∀ F : Distribution 3 R, NestedSupport F → NestedSupport (polynomialAction q F))
    (kill : ∀ F : Distribution 3 R, NestedSupport F → polynomialAction q F = 0 → F = 0)
    (n : ℕ) (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction (q ^ n) F = 0) : F = 0 := by
  induction n generalizing F with
  | zero => simpa using hz
  | succ n ih =>
    rw [pow_succ', map_mul, Module.End.mul_apply] at hz
    exact ih F hF (kill _ (power_preserves q closed n F hF) hz)

private theorem variable_zero (i : Fin 3) (F : Distribution 3 R)
    (hz : polynomialAction (variablePolynomial i) F = 0) : F = 0 := by
  funext e
  have h := congrFun hz (e + Pi.single i 1)
  rw [variable_action, add_sub_cancel_right] at h
  exact h

/-- Only the existing supported positive reconstruction cancels a row. -/
private theorem positive_row_zero (I : ℤ → ℤ → R) (B : ℕ)
    (lower : ∀ y z : ℤ, y < -(B : ℤ) → I y z = 0)
    (hz : ∀ y z : ℤ, positiveClear 1 I y z = 0) : ∀ y z : ℤ, I y z = 0 := by
  intro y z
  by_cases hy : 0 ≤ y + B
  · rw [supported_positive_reconstruction I 1 B lower y z hy]
    simp only [hz, smul_zero, Finset.sum_const_zero]
  · exact lower y z (by omega)

private theorem xy_zero (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction (variablePolynomial 0 + variablePolynomial 1) F = 0) : F = 0 := by
  obtain ⟨U, hu⟩ := hF.1
  have vanish (z : ℤ) : ∀ x y : ℤ, F ![x, y, z] = 0 := by
    apply positive_row_zero (fun x y => F ![x, y, z]) U (fun x y hx => hu x y z hx)
    intro x y
    have h := congrFun hz ![x, y + 1, z]
    rw [xy_action] at h
    simpa [positiveClear, Finset.sum_range_succ, add_comm] using h
  funext e
  change F e = 0
  have h := vanish (e 2) (e 0) (e 1)
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [ee] using h

private theorem yz_zero (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction (variablePolynomial 1 + variablePolynomial 2) F = 0) : F = 0 := by
  have vanish (x : ℤ) : ∀ y z : ℤ, F ![x, y, z] = 0 := by
    obtain ⟨B, hb⟩ := hF.2 x
    apply positive_row_zero (fun y z => F ![x, y, z]) B hb
    intro y z
    have h := congrFun hz ![x, y, z + 1]
    rw [yz_action] at h
    simpa [positiveClear, Finset.sum_range_succ, add_comm] using h
  funext e
  change F e = 0
  have h := vanish (e 0) (e 1) (e 2)
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [ee] using h

/-- At the first surviving x row, only y+z remains. Its inverse is legal
because THAT row has its own y bound. Earlier x rows vanish by induction. -/
private theorem triple_zero (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction
      (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) F = 0) : F = 0 := by
  obtain ⟨U, hu⟩ := hF.1
  have rows : ∀ n : ℕ, ∀ y z : ℤ, F ![(n : ℤ) - U, y, z] = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have prev (y z : ℤ) : F ![(n : ℤ) - U - 1, y, z] = 0 := by
        by_cases hn : n = 0
        · apply hu
          omega
        · have hp := ih (n - 1) (by omega) y z
          have eq : ((n - 1 : ℕ) : ℤ) - U = (n : ℤ) - U - 1 := by omega
          simpa only [eq] using hp
      obtain ⟨B, hb⟩ := hF.2 ((n : ℤ) - U)
      apply positive_row_zero (fun y z => F ![(n : ℤ) - U, y, z]) B hb
      intro y z
      have h := congrFun hz ![(n : ℤ) - U, y, z + 1]
      rw [triple_action, prev] at h
      simpa [positiveClear, Finset.sum_range_succ, add_comm] using h
  funext e
  change F e = 0
  by_cases hx : 0 ≤ e 0 + U
  · have h := rows (e 0 + U).toNat (e 1) (e 2)
    have nx : ((e 0 + U).toNat : ℤ) - U = e 0 := by
      rw [Int.toNat_of_nonneg hx]
      omega
    rw [nx] at h
    have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
      funext i
      fin_cases i <;> rfl
    simpa only [ee] using h
  · have h := hu (e 0) (e 1) (e 2) (by omega)
    have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
      funext i
      fin_cases i <;> rfl
    simpa only [ee] using h

/-- Concrete R-specific kernel theorem. Signed translations remove only
monomials; positive factors are removed on actual nested-supported channels. -/
private theorem finalR_zero (k A C D : ℕ) (F : Distribution 3 R)
    (hF : NestedSupport F)
    (hz : polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ A *
        (variablePolynomial 1 + variablePolynomial 2) ^ C * variablePolynomial 2 ^ D) F = 0) :
    F = 0 := by
  let X : LaurentPolynomial 3 := variablePolynomial 0
  let Y : LaurentPolynomial 3 := variablePolynomial 1
  let Z : LaurentPolynomial 3 := variablePolynomial 2
  have cx (i : Fin 3) := variable_preserves (R := R) i
  have cxy : ∀ G : Distribution 3 R, NestedSupport G →
      NestedSupport (polynomialAction (X + Y) G) := by
    intro G hG
    simpa only [X, Y, map_add, LinearMap.add_apply] using
      nested_add _ _ (cx 0 G hG) (cx 1 G hG)
  have cyz : ∀ G : Distribution 3 R, NestedSupport G →
      NestedSupport (polynomialAction (Y + Z) G) := by
    intro G hG
    simpa only [Y, Z, map_add, LinearMap.add_apply] using
      nested_add _ _ (cx 1 G hG) (cx 2 G hG)
  have ct : ∀ G : Distribution 3 R, NestedSupport G →
      NestedSupport (polynomialAction (X + Y + Z) G) := by
    intro G hG
    simpa only [Z, map_add, LinearMap.add_apply] using
      nested_add _ _ (cxy G hG) (cx 2 G hG)
  let Fz := polynomialAction (Z ^ D) F
  let Fyz := polynomialAction ((Y + Z) ^ C) Fz
  let Ft := polynomialAction ((X + Y + Z) ^ A) Fyz
  let Fxy := polynomialAction ((X + Y) ^ k) Ft
  let Fy := polynomialAction (Y ^ k) Fxy
  have sz : NestedSupport Fz := power_preserves Z (cx 2) D F hF
  have syz : NestedSupport Fyz := power_preserves (Y + Z) cyz C Fz sz
  have st : NestedSupport Ft := power_preserves (X + Y + Z) ct A Fyz syz
  have sxy : NestedSupport Fxy := power_preserves (X + Y) cxy k Ft st
  have sy : NestedSupport Fy := power_preserves Y (cx 1) k Fxy sxy
  have hx : polynomialAction (X ^ k) Fy = 0 := by
    simpa only [X, Y, Z, Fy, Fxy, Ft, Fyz, Fz,
      map_mul, Module.End.mul_apply] using hz
  have hy : Fy = 0 := power_zero X (cx 0) (fun G _ h => variable_zero 0 G h) k Fy sy hx
  have hxy : Fxy = 0 := power_zero Y (cx 1)
    (fun G _ h => variable_zero 1 G h) k Fxy sxy hy
  have ht : Ft = 0 := power_zero (X + Y) cxy xy_zero k Ft st hxy
  have hyz : Fyz = 0 := power_zero (X + Y + Z) ct triple_zero A Fyz syz ht
  have hz' : Fz = 0 := power_zero (Y + Z) cyz yz_zero C Fz sz hyz
  exact power_zero Z (cx 2) (fun G _ h => variable_zero 2 G h) D F hF hz'

/-- Faithful injectivity for the exact final R and the real nested support. -/
theorem finalR_injective (k A C D : ℕ) (F G : Distribution 3 R)
    (hF : NestedSupport F) (hG : NestedSupport G)
    (same : polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ A *
        (variablePolynomial 1 + variablePolynomial 2) ^ C * variablePolynomial 2 ^ D) F =
      polynomialAction
      (variablePolynomial 0 ^ k * variablePolynomial 1 ^ k *
        (variablePolynomial 0 + variablePolynomial 1) ^ k *
        (variablePolynomial 0 + variablePolynomial 1 + variablePolynomial 2) ^ A *
        (variablePolynomial 1 + variablePolynomial 2) ^ C * variablePolynomial 2 ^ D) G) :
    F = G := by
  apply sub_eq_zero.mp
  apply finalR_zero k A C D (F - G) (nested_sub F G hF hG)
  rw [map_sub, same, sub_self]

end
end D5.S3.VertexAlgebra.SupportedFinalRInjectivity
