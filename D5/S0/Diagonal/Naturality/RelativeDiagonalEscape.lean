/- GID: D5/S0/Diagonal/Naturality/RelativeDiagonalEscape
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/RelativeDiagonalEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free twist sends every diagonal listing outside its range. -/

module
prelude
public import OmegaInit.Core

namespace D5.S0.Diagonal.Naturality.RelativeDiagonalEscape

open Omega

/-- The diagonal obtained from a fixed-point-free twist cannot be a row of the original listing. -/
public theorem relative_diagonal_escape {A : Type u} {Y : Type v}
    (listing : A → A → Y) (twist : Y → Y)
    (fixedPointFree : ∀ value, Not (Eq (twist value) value)) :
    Not (Omega.Exists (fun row =>
      Eq (listing row) (fun index => twist (listing index index)))) :=
  fun captured =>
    captured.elim (fun row equal =>
      fixedPointFree (listing row row)
        (Omega.congrArg (fun line : A → Y => line row) equal).symm)

private inductive OneIndex where
  | only

example : OneIndex := .only

example :
    Not (Omega.Exists (fun row : OneIndex =>
      Eq ((fun _ _ : OneIndex => Bool.false) row) (fun _ : OneIndex => Bool.true))) :=
  relative_diagonal_escape (fun _ _ : OneIndex => Bool.false)
    (Bool.rec (motive := fun _ => Bool) .true .false)
    (have distinct : Not (Eq Bool.false Bool.true) :=
      fun equal => Eq.subst (motive := Bool.rec (motive := fun _ => Prop) Omega.True False) equal Omega.True.intro
     Bool.rec (fun equal => distinct equal.symm) distinct)

end D5.S0.Diagonal.Naturality.RelativeDiagonalEscape
