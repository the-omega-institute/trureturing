/- GID: D5/S1/Words/Powers/ConjugacyNormalForm
   generality: G
   mirror-B: D5/B/S1/Words/Powers/ConjugacyNormalForm
   mirror-E: none(waiver:universal-symbolic-word-classification)
   anchors: []
   utility: none
   digest: A nonempty word conjugacy has a unique literal exponent and short cut. -/

module

public import D5.S1.Words.Powers.WordPower
public import OmegaMath.Algebra.FreeMonoid.Conjugacy
import OmegaChecks.NatCorrespondence

/-! Literal List interpretation of length-graded word conjugacy.

The publication entry is the Blueprint theorem `unique-short-cut-normal-form`.
The mathematical length descent and uniqueness argument are supplied by
Omega.FreeMonoid.Conjugacy; all its elementary laws are proved here for List.
-/

public section

namespace D5.S1.Words.Powers.ConjugacyNormalForm

open OmegaChecks.NatCorrespondence
namespace G
export Omega.FreeMonoid.Conjugacy (Laws Normal exists_normal normal_sound normal_unique)
end G

universe u
variable {α : Type u}

private theorem toOmegaEq {A : Sort v} {a b : A} (h : a = b) : Omega.Eq a b := by
  cases h
  exact Omega.rfl

private theorem toStd_injective {m n : Omega.Nat} (h : toStd m = toStd n) : m = n :=
  (fromStd_toStd m).symm.trans ((congrArg fromStd h).trans (fromStd_toStd n))

private def listLength (w : List α) : Omega.Nat := fromStd w.length
private noncomputable def listPower (n : Omega.Nat) (w : List α) : List α :=
  wordPower (toStd n) w

private theorem length_le_iff (a b : Nat) :
    Omega.Nat.le (fromStd a) (fromStd b) ↔ a ≤ b := by
  simpa only [toStd_fromStd] using (toStd_le_iff (fromStd a) (fromStd b)).symm

private theorem length_lt_iff (a b : Nat) :
    Omega.Nat.lt (fromStd a) (fromStd b) ↔ a < b := by
  simpa only [Omega.Nat.lt, Nat.succ_le_iff,
    show toStd (Omega.Nat.succ (fromStd a)) = (toStd (fromStd a)).succ from rfl,
    toStd_fromStd] using
    (toStd_le_iff (Omega.Nat.succ (fromStd a)) (fromStd b)).symm

private theorem listLaws : G.Laws ([] : List α) List.append listLength listPower := by
  refine Omega.And.intro ?_ (Omega.And.intro ?_ (Omega.And.intro ?_
    (Omega.And.intro ?_ (Omega.And.intro ?_ (Omega.And.intro ?_ ?_)))))
  · intro a b c
    exact toOmegaEq (List.append_assoc a b c)
  · intro a
    exact toOmegaEq (List.nil_append a)
  · intro a b c h
    exact toOmegaEq (List.append_cancel_left (fromOmegaEq h))
  · intro a b
    exact toOmegaEq (toStd_injective (by
      change toStd (fromStd (a ++ b).length) = toStd ((fromStd a.length).add (fromStd b.length))
      rw [toStd_add, toStd_fromStd, toStd_fromStd, toStd_fromStd, List.length_append]))
  · intro a
    exact toOmegaEq (wordPower_zero a)
  · intro n a
    exact toOmegaEq (wordPower_succ (toStd n) a)
  · intro a b c d h hlen
    have hstd := fromOmegaEq h
    have hle : a.length ≤ c.length := (length_le_iff _ _).mp hlen
    rcases List.append_eq_append_iff.mp hstd with ⟨r, hc, hb⟩ | ⟨r, ha, hd⟩
    · exact Omega.Exists.intro r (Omega.And.intro (toOmegaEq hc) (toOmegaEq hb))
    · have hr : r = [] := by
        have hh := congrArg List.length ha
        rw [List.length_append] at hh
        exact List.length_eq_zero_iff.mp (by omega)
      subst r
      have hac : a = c := by simpa using ha
      have hbd : b = d := List.append_cancel_left (hac ▸ hstd)
      exact Omega.Exists.intro [] (Omega.And.intro
        (toOmegaEq (by simpa using hac.symm)) (toOmegaEq (by simpa using hbd)))

private theorem normal_iff (a b z : List α) (n : Omega.Nat) (p q : List α) :
    G.Normal List.append listLength listPower a b z n p q ↔
      a = p ++ q ∧ b = q ++ p ∧ z = wordPower (toStd n) a ++ p ∧ p.length < a.length := by
  constructor
  · intro h
    exact ⟨fromOmegaEq h.left, fromOmegaEq h.right.left, fromOmegaEq h.right.right.left,
      (length_lt_iff _ _).mp h.right.right.right⟩
  · rintro ⟨ha, hb, hz, hp⟩
    exact Omega.And.intro (toOmegaEq ha) (Omega.And.intro (toOmegaEq hb)
      (Omega.And.intro (toOmegaEq hz) ((length_lt_iff _ _).mpr hp)))

/-- For a fixed conjugating word, the complete exponent/prefix/suffix triple is unique.
The alphabet is arbitrary; zero exponents and empty cut prefixes remain in scope. -/
theorem conjugacy_iff_exists_unique_short_cut (a b z : List α) (ha : a ≠ []) :
    a ++ z = z ++ b ↔ ∃! t : Nat × List α × List α,
      a = t.2.1 ++ t.2.2 ∧ b = t.2.2 ++ t.2.1 ∧
        z = wordPower t.1 a ++ t.2.1 ∧ t.2.1.length < a.length := by
  constructor
  · intro equation
    have positive : Omega.Nat.lt Omega.Nat.zero (listLength a) :=
      (length_lt_iff 0 a.length).mpr (List.length_pos_of_ne_nil ha)
    exact (G.exists_normal listLaws a b z positive (toOmegaEq equation)).elim (fun n hn =>
      hn.elim (fun p hp => hp.elim (fun q normal => by
        refine ⟨(toStd n, p, q), (normal_iff a b z n p q).mp normal, ?_⟩
        rintro ⟨m, r, s⟩ competitor
        have other : G.Normal List.append listLength listPower a b z (fromStd m) r s :=
          (normal_iff a b z (fromStd m) r s).mpr
            (by simpa only [toStd_fromStd] using competitor)
        have unique := G.normal_unique listLaws a b z (fromStd m) n r s p q
          other normal
        have hn : m = toStd n := by
          simpa only [toStd_fromStd] using congrArg toStd (fromOmegaEq unique.left)
        exact Prod.ext hn (Prod.ext (fromOmegaEq unique.right.left) (fromOmegaEq unique.right.right)))))
  · rintro ⟨⟨n, p, q⟩, normal, _⟩
    have converted : G.Normal List.append listLength listPower a b z (fromStd n) p q :=
      (normal_iff a b z (fromStd n) p q).mpr (by simpa only [toStd_fromStd] using normal)
    exact fromOmegaEq (G.normal_sound listLaws a b z (fromStd n) p q converted)

end D5.S1.Words.Powers.ConjugacyNormalForm
