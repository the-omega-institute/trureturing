module
prelude
public import OmegaInit.Data.String.Lemmas.Pattern.Basic
import all OmegaInit.Data.String.Lemmas.Splits

namespace Omega.String.Slice.Pattern.Model

/-- The NUL character has UTF-8 byte length one. -/
private abbrev subject := (String.singleton (Char.ofNat Nat.zero)).toSlice
private abbrev token := (PUnit.unit : Unit)
private abbrev acceptsEmptyOr (P : Prop) : PatternModel token :=
  ⟨fun s => Or (Eq s (String.ofList List.nil)) P⟩

private theorem startBeforeEnd :
    Nat.lt subject.startPos.offset.byteIdx subject.endPos.offset.byteIdx :=
  Nat.lt_succ_self Nat.zero

/-- A longest prefix for every pattern decides any proposition on the one-character slice. -/
public theorem _root_.OmegaStrictString.excludedMiddleOfLongest
    (longest : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
      IsMatch pat pos → Exists (fun next : s.Pos => IsLongestMatch pat next))
    (P : Prop) : Or P (Not P) :=
  let model : PatternModel token := acceptsEmptyOr P
  let start : @IsMatch _ token model subject subject.startPos :=
    ⟨Or.inl String.Slice.copy_sliceTo_startPos⟩
  (@longest _ token model subject _ start).elim fun q h =>
    Or.elim h.isMatch.matches_copy
      (fun empty => Or.inr fun yes =>
        h.not_isMatch subject.endPos
          (Eq.subst (motive := fun p : subject.Pos => Nat.lt p.offset.byteIdx subject.endPos.offset.byteIdx)
            (q.splits.eq_startPos_iff.mpr empty).symm startBeforeEnd) ⟨Or.inr yes⟩)
      Or.inl

/-- The same language tests the longest suffix by reversing the endpoint comparison. -/
public theorem _root_.OmegaStrictString.excludedMiddleOfRevLongest
    (longest : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos},
      IsRevMatch pat pos → Exists (fun next : s.Pos => IsLongestRevMatch pat next))
    (P : Prop) : Or P (Not P) :=
  let model : PatternModel token := acceptsEmptyOr P
  let stop : @IsRevMatch _ token model subject subject.endPos :=
    ⟨Or.inl String.Slice.copy_sliceFrom_endPos⟩
  (@longest _ token model subject _ stop).elim fun q h =>
    Or.elim h.isRevMatch.matches_copy
      (fun empty => Or.inr fun yes =>
        h.not_isRevMatch subject.startPos
          (Eq.subst (motive := fun p : subject.Pos => Nat.lt subject.startPos.offset.byteIdx p.offset.byteIdx)
            (q.splits.eq_endPos_iff.mpr empty).symm startBeforeEnd) ⟨Or.inr yes⟩)
      Or.inl

end Omega.String.Slice.Pattern.Model
