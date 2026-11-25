/- GID: D5/S3/Combinatorics/Matroids/SteinerSwitchCentre
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerSwitchCentre
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Noncentral points of a Steiner loop are exactly the deletions admitting a maximal switch. -/

import D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches
import Mathlib.Algebra.Group.Center

/-! # Central points and point-deleted Steiner switches -/

namespace D5.S3.Combinatorics.Matroids.SteinerSwitchCentre

open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open PointDeletedSteinerSwitch (pointDeletedFamily point_deleted_switch)
open SteinerMatchingTranslations
open SteinerAlternatingSwitches (SuccessfulStart)

variable {r : ℕ} {S : Set (Set (Fin (r + 1)))}
variable (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)

/-- The usual Steiner loop product, with the adjoined point represented by none. -/
@[instance_reducible]
noncomputable def steinerMul : Mul (Option (Fin (r + 1))) where
  mul
    | none, x => x
    | some q, x => translate valid complete q x

theorem product_comm (x y : Option (Fin (r + 1))) :
    letI := steinerMul valid complete
    x * y = y * x := by
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some b => exact (translate_none valid complete b).symm
  | some a =>
      cases y with
      | none => exact translate_none valid complete a
      | some b =>
          change translate valid complete a (some b) = translate valid complete b (some a)
          by_cases eq : a = b
          · subst b
            rfl
          · obtain ⟨z, _, _, hab, hba⟩ := translate_special_square valid complete eq
            exact hab.trans hba.symm

private theorem commute_square {X : Type*} {Q V : X → X}
    (hQ : Function.Involutive Q) (hV : Function.Involutive V)
    {e : X} (eq0 : Q (V e) = V (Q e)) :
    Q (V (Q e)) = V (Q (Q e)) ∧
      Q (V (V e)) = V (Q (V e)) ∧
      Q (V (Q (V e))) = V (Q (Q (V e))) := by
  have qTwice (x : X) : Q (Q x) = x := hQ x
  have vTwice (x : X) : V (V x) = x := hV x
  refine ⟨?_, ?_, ?_⟩
  · simp only [← eq0, qTwice]
  · simp only [eq0, vTwice]
  · calc
      Q (V (Q (V e))) = Q (V (V (Q e))) := congrArg (Q ∘ V) eq0
      _ = e := by simp only [vTwice, qTwice]
      _ = V (Q (Q (V e))) := by simp only [qTwice, vTwice]

/-- A deleted point has a successful switch for some retained pivot and start. -/
def AdmitsSwitch (S : Set (Set (Fin (r + 1)))) (q : Fin (r + 1)) : Prop :=
  ∃ m : Fin r → Fin r,
    (∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b) ∧
    ∃ v a, SuccessfulStart (pointDeletedFamily S q) m v a

private theorem no_switch_iff_central (q : Fin (r + 1)) :
    ∃ m : Fin r → Fin r,
      (∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b) ∧
      ((¬ ∃ v a, SuccessfulStart (pointDeletedFamily S q) m v a) ↔
        @IsMulCentral _ (steinerMul valid complete) (some q)) := by
  classical
  obtain ⟨_, m, inv, _, leave, switch⟩ := point_deleted_switch S valid complete q
  refine ⟨m, leave, ?_⟩
  let _ : Mul (Option (Fin (r + 1))) := steinerMul valid complete
  have comm := product_comm valid complete
  constructor
  · intro failure
    have allComm (v x : Option (Fin (r + 1))) :
        some q * (v * x) = v * (some q * x) := by
      cases v with
      | none => rfl
      | some vLabel =>
          change translate valid complete q (translate valid complete vLabel x) =
            translate valid complete vLabel (translate valid complete q x)
          by_cases hv : vLabel = q
          · subst vLabel
            rfl
          · obtain ⟨v, rfl⟩ := Fin.exists_succAbove_eq hv
            let Q := translate valid complete q
            let V := translate valid complete (q.succAbove v)
            change Q (V x) = V (Q x)
            have eq0 : Q (V none) = V (Q none) := comm (some q) (some (q.succAbove v))
            have square := commute_square (translate_involutive valid complete q)
              (translate_involutive valid complete (q.succAbove v)) eq0
            cases x with
            | none => exact eq0
            | some xLabel =>
                by_cases hx : xLabel = q
                · subst xLabel
                  exact square.1
                · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hx
                  by_cases hva : v = a
                  · subst a
                    exact square.2.1
                  · by_cases hvm : v = m a
                    · have ha : m v = a := by rw [hvm, inv a]
                      have hcorner : Q (V none) = some (q.succAbove a) := by
                        change translate valid complete q (some (q.succAbove v)) =
                          some (q.succAbove a)
                        exact (translate_deleted_match valid complete q leave v).trans
                          (congrArg (fun x => some (q.succAbove x)) ha)
                      rw [← hcorner]
                      exact square.2.2
                    · obtain ⟨b, d, hb, hd, _, _, _, _, _⟩ := switch a v hva hvm
                      have joined : d = m b := by
                        by_contra nde
                        exact failure ⟨v, a, hva, hvm, b, d, hb, hd, nde⟩
                      exact ((switch_commutes_iff valid complete q leave hva hvm hb hd).mpr joined).symm
    refine ⟨comm (some q), ?_, ?_⟩
    · intro x y
      calc
        some q * (x * y) = some q * (y * x) := congrArg (some q * ·) (comm x y)
        _ = y * (some q * x) := allComm y x
        _ = (some q * x) * y := comm _ _
    · intro x y
      calc
        (x * y) * some q = some q * (x * y) := comm _ _
        _ = x * (some q * y) := allComm x y
        _ = x * (y * some q) := congrArg (x * ·) (comm _ _)
  · intro central
    rintro ⟨v, a, hva, hvm, b, d, hb, hd, nde⟩
    have equal := central.left_comm (some (q.succAbove v)) (some (q.succAbove a))
    exact nde ((switch_commutes_iff valid complete q leave hva hvm hb hd).mp equal.symm)


/-- A deleted point admits a maximal switch exactly when it is noncentral. -/
theorem admits_switch_iff_not_central (q : Fin (r + 1)) :
    AdmitsSwitch S q ↔ ¬ @IsMulCentral _ (steinerMul valid complete) (some q) := by
  classical
  obtain ⟨m, leave, centre⟩ := no_switch_iff_central valid complete q
  constructor
  · rintro ⟨m', leave', hs⟩ central
    have eq : m' = m := funext fun a =>
      (leave a (m' a)).mp ((leave' a (m' a)).mpr rfl) |>.symm
    subst m'
    exact (centre.mpr central) hs
  · intro noncentral
    refine ⟨m, leave, ?_⟩
    by_contra failure
    exact noncentral (centre.mp failure)

/-- Exactly the original points outside the centre admit a switch. -/
theorem ncard_admits_switch :
    let _ : Mul (Option (Fin (r + 1))) := steinerMul valid complete
    ({q | AdmitsSwitch S q} : Set (Fin (r + 1))).ncard =
      r + 2 - (Set.center (Option (Fin (r + 1)))).ncard := by
  let _ : Mul (Option (Fin (r + 1))) := steinerMul valid complete
  let Z := Set.center (Option (Fin (r + 1)))
  have identity : none ∈ Z := by
    have left (x : Option (Fin (r + 1))) : none * x = x := rfl
    have right (x : Option (Fin (r + 1))) : x * none = x :=
      (product_comm valid complete x none).trans (left x)
    exact ⟨fun x => (left x).trans (right x).symm,
      fun x y => by simp only [left], fun x y => by simp only [right]⟩
  have image : (some : Fin (r + 1) → Option (Fin (r + 1))) '' {q | AdmitsSwitch S q} = Zᶜ := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (admits_switch_iff_not_central valid complete q).mp hq
    · intro hx
      cases x with
      | none => exact (hx identity).elim
      | some q => exact ⟨q, (admits_switch_iff_not_central valid complete q).mpr hx, rfl⟩
  change ({q | AdmitsSwitch S q} : Set (Fin (r + 1))).ncard = r + 2 - Z.ncard
  rw [← Set.ncard_image_of_injective _ (Option.some_injective _), image, Set.ncard_compl]
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]

end D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
