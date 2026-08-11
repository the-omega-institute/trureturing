/- GID: D5/S1/Recurrence/BivariateWordSeries
   generality: I
   mirror-B: D5/B/S1/Recurrence/BivariateWordSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admissible-word bookkeeping obeys its bivariate self-substitution equation. -/

import Mathlib.Logic.Equiv.Sum
import Mathlib.SetTheory.Cardinal.Defs

namespace D5.S1.Recurrence.BivariateWordSeries

/-- A nonempty finite binary word with no adjacent occupied positions, read
from its lowest position. -/
inductive NonemptyWord where
  | single
  | skip (rest : NonemptyWord)
  | take (rest : NonemptyWord)

/-- The empty word together with the nonempty admissible words. -/
abbrev Word := Option NonemptyWord

/-- The two bookkeeping exponents of a word. -/
abbrev Degree := ℕ × ℕ

/-- Substitution `(u, v) -> (v, uv)` on monomial exponents. -/
def skipDegree (degree : Degree) : Degree :=
  (degree.2, degree.1 + degree.2)

/-- Multiplication by `u` after substitution `(u, v) -> (uv, uv^2)`. -/
def takeDegree (degree : Degree) : Degree :=
  (degree.1 + degree.2 + 1, degree.1 + 2 * degree.2)

/-- The exponent pair carried by a nonempty admissible word. -/
def nonemptyDegree : NonemptyWord → Degree
  | .single => (1, 0)
  | .skip rest => skipDegree (nonemptyDegree rest)
  | .take rest => takeDegree (nonemptyDegree rest)

/-- The empty word has constant degree; nonempty words use their recursive
bookkeeping degree. -/
def wordDegree : Word → Degree
  | none => (0, 0)
  | some word => nonemptyDegree word

/-- Lowest-position decomposition: an admissible word either skips that
position or occupies it and therefore skips the next position. -/
private def wordSplitEquiv : Word ≃ Word ⊕ Word where
  toFun
    | none => Sum.inl none
    | some .single => Sum.inr none
    | some (.skip rest) => Sum.inl (some rest)
    | some (.take rest) => Sum.inr (some rest)
  invFun
    | Sum.inl none => none
    | Sum.inl (some rest) => some (.skip rest)
    | Sum.inr none => some .single
    | Sum.inr (some rest) => some (.take rest)
  left_inv word := by
    cases word with
    | none => rfl
    | some word => cases word <;> rfl
  right_inv branch := by
    cases branch with
    | inl word => cases word <;> rfl
    | inr word => cases word <;> rfl

private theorem degree_split (word : Word) :
    wordDegree word =
      match wordSplitEquiv word with
      | Sum.inl rest => skipDegree (wordDegree rest)
      | Sum.inr rest => takeDegree (wordDegree rest) := by
  cases word with
  | none => rfl
  | some word => cases word <;> rfl

/-- Cardinal-valued coefficients of the bivariate admissible-word series. -/
def bookkeepingSeries (degree : Degree) : Cardinal :=
  Cardinal.mk {word : Word // wordDegree word = degree}

/-- Coefficients after the substitution `(u, v) -> (v, uv)`. -/
def skipBranchSeries (degree : Degree) : Cardinal :=
  Cardinal.mk {word : Word // skipDegree (wordDegree word) = degree}

/-- Coefficients after the substitution `(u, v) -> (uv, uv^2)` and
multiplication by `u`. -/
def takeBranchSeries (degree : Degree) : Cardinal :=
  Cardinal.mk {word : Word // takeDegree (wordDegree word) = degree}

private def branchPredicate (degree : Degree) : Word ⊕ Word → Prop
  | Sum.inl word => skipDegree (wordDegree word) = degree
  | Sum.inr word => takeDegree (wordDegree word) = degree

private def coefficientSplit (degree : Degree) :
    {word : Word // wordDegree word = degree} ≃
      {word : Word // skipDegree (wordDegree word) = degree} ⊕
        {word : Word // takeDegree (wordDegree word) = degree} :=
  (wordSplitEquiv.subtypeEquiv
      (p := fun word => wordDegree word = degree)
      (q := branchPredicate degree) fun word => by
    rw [degree_split]
    cases wordSplitEquiv word <;> simp [branchPredicate])
    |>.trans (Equiv.subtypeSum (p := branchPredicate degree))

/-- The coefficientwise form of
`F(u, v) = F(v, uv) + u * F(uv, uv^2)`: splitting an admissible word at its
lowest position gives the two substituted branches exactly. -/
theorem bookkeeping_series_self_functional_equation :
    bookkeepingSeries =
      fun degree => skipBranchSeries degree + takeBranchSeries degree := by
  funext degree
  change Cardinal.mk {word : Word // wordDegree word = degree} =
    Cardinal.mk {word : Word // skipDegree (wordDegree word) = degree} +
      Cardinal.mk {word : Word // takeDegree (wordDegree word) = degree}
  simpa only [Cardinal.mk_sum, Cardinal.lift_id] using
    Cardinal.mk_congr (coefficientSplit degree)

end D5.S1.Recurrence.BivariateWordSeries
