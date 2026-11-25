/- GID: D5/S3/Combinatorics/Matroids/SteinerSwitchOrbit
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerSwitchOrbit
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The Steiner loop centre divides the number of successful starts at a fixed pivot. -/

/-
successful_starts_dvd_center
  proof_shape: content
  admission_basis: escape-witness
  escape_witness: the successful vertices form central-translation orbits each
    bijective with the centre, using the action on the two matching edges.
  Direct frozen dependencies: SteinerSwitchCentre.steinerMul,
    SteinerMatchingTranslations.translate_involutive,
    SteinerMatchingTranslations.translate_none,
    SteinerAlternatingSwitches.point_deleted_successful_starts.
-/

import D5.S3.Combinatorics.Matroids.SteinerSwitchCentre

/-! # Central translation orbits of Steiner switches -/

open Function Set SimpleGraph
open scoped BigOperators

namespace D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit

/-- Each orbit of central translations in the stable set has the cardinality of the centre. -/
private theorem center_dvd_stable_card {L : Type*} [Finite L] [Mul L]
    (e : L) (he : e ∈ Set.center L) (hunit : ∀ x : L, e * x = x)
    (hinvol : ∀ x y : L, x * (x * y) = y) (D : Set L)
    (hstable : ∀ z ∈ Set.center L, ∀ x ∈ D, z * x ∈ D) :
    (Set.center L).ncard ∣ D.ncard := by
  classical
  let R : Setoid D := {
    r := fun a b => ∃ z ∈ Set.center L, z * a.val = b.val
    iseqv := ⟨
      fun a => ⟨e, he, hunit a.val⟩,
      fun {a b} ⟨z, hz, hab⟩ => ⟨z, hz, by rw [← hab, hinvol]⟩,
      fun {a b c} ⟨z, hz, hab⟩ ⟨w, hw, hbc⟩ =>
        ⟨w * z, Set.mul_mem_center hw hz, by
          rw [← (Set.mem_center_iff.mp hw).left_assoc, hab, hbc]⟩⟩ }
  let f : D → Quotient R := Quotient.mk R
  let _ : Fintype D := Fintype.ofFinite _
  let _ : Fintype (Quotient R) := Fintype.ofFinite _
  let _ : Fintype (Set.center L) := Fintype.ofFinite _
  let _ : (q : Quotient R) → Fintype {x // f x = q} := fun _ => Fintype.ofFinite _
  have fiberCard (q : Quotient R) :
      Fintype.card {x // f x = q} = Fintype.card (Set.center L) := by
    induction q using Quotient.inductionOn with
    | _ a =>
      let shift : Set.center L → {x // f x = Quotient.mk R a} :=
        fun z => ⟨⟨z.val * a.val, hstable z.val z.prop a.val a.prop⟩,
          Quotient.sound (s := R) ⟨z.val, z.prop, hinvol z.val a.val⟩⟩
      have bijective : Bijective shift := by
        constructor
        · intro z w h
          apply Subtype.ext
          have eq : z.val * a.val = w.val * a.val :=
            congrArg (fun x => x.val.val) h
          rw [(Set.mem_center_iff.mp z.prop).comm, (Set.mem_center_iff.mp w.prop).comm] at eq
          exact (show Involutive (a.val * ·) from hinvol a.val).injective eq
        · intro b
          have related : R.r a b.val := Quotient.exact b.prop.symm
          obtain ⟨z, hz, hza⟩ := related
          exact ⟨⟨z, hz⟩, Subtype.ext (Subtype.ext hza)⟩
      exact (Fintype.card_congr (Equiv.ofBijective shift bijective)).symm
  change Nat.card (Set.center L) ∣ Nat.card D
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  exact Finset.dvd_sum (fun q _ => (fiberCard q).symm ▸ dvd_refl _)

open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open SteinerMatchingTranslations
open SteinerAlternatingSwitches (pivotGraph SuccessfulStart point_deleted_successful_starts)
open SteinerSwitchCentre (steinerMul)

/-- The number of successful starts for a fixed deletion and pivot is divisible by the centre size. -/
theorem successful_starts_dvd_center {r : ℕ} (q : Fin (r + 1))
    (m : Fin r → Fin r) (v : Fin r) (S : Set (Set (Fin (r + 1))))
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (leave : ∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b) :
    let _ := steinerMul valid complete
    (Set.center (Option (Fin (r + 1)))).ncard ∣
      ({a | SuccessfulStart (pointDeletedFamily S q) m v a} : Set (Fin r)).ncard := by
  classical
  let _ := steinerMul valid complete
  have hinvol (x y : Option (Fin (r + 1))) : x * (x * y) = y := by
    cases x with
    | none => rfl
    | some x => exact translate_involutive valid complete x y
  have mul_none (x : Option (Fin (r + 1))) : x * none = x := by
    cases x with
    | none => rfl
    | some x => exact translate_none valid complete x
  have hcentre : (none : Option (Fin (r + 1))) ∈ Set.center _ := by
    refine ⟨fun x => (mul_none x).symm, fun x y => rfl, ?_⟩
    intro x y
    rw [mul_none, mul_none]
  obtain ⟨_, canonical, canonicalLeave, counts⟩ :=
    point_deleted_successful_starts S valid complete q
  have eq : canonical = m := funext fun a =>
    ((leave a (canonical a)).mp ((canonicalLeave a (canonical a)).mpr rfl)).symm
  subst canonical
  let G := pivotGraph valid complete q v
  let large : Set (Option (Fin (r + 1))) := {x | 6 ≤ (G.connectedComponentMk x).supp.ncard}
  have stable (z : Option (Fin (r + 1))) (hz : z ∈ Set.center _) (x : Option (Fin (r + 1)))
      (hx : x ∈ large) : z * x ∈ large := by
    let τ := Involutive.toPerm (z * ·) (hinvol z)
    let iso : G ≃g G := {
      toEquiv := τ
      map_rel_iff' := by
        intro a b
        change ((some q * (z * a) = z * b) ∨ (some (q.succAbove v) * (z * a) = z * b)) ↔
          ((some q * a = b) ∨ (some (q.succAbove v) * a = b))
        rw [← (Set.mem_center_iff.mp hz).left_comm, ← (Set.mem_center_iff.mp hz).left_comm]
        exact or_congr τ.injective.eq_iff τ.injective.eq_iff }
    have e := SimpleGraph.ConnectedComponent.isoEquivSupp iso (G.connectedComponentMk x)
    have hc : (G.connectedComponentMk x).supp.ncard =
        (G.connectedComponentMk (z * x)).supp.ncard := by
      exact Nat.card_congr e
    change 6 ≤ (G.connectedComponentMk x).supp.ncard at hx
    change 6 ≤ (G.connectedComponentMk (z * x)).supp.ncard
    rwa [← hc]
  have d := center_dvd_stable_card none hcentre (fun _ => rfl) hinvol large stable
  have inj : Injective (Option.some ∘ q.succAbove) :=
    (Option.some_injective _).comp Fin.succAbove_right_injective
  have heq : (Option.some ∘ q.succAbove) '' {a | SuccessfulStart (pointDeletedFamily S q) m v a} =
      large := (counts v).2.1
  rw [← heq, Set.ncard_image_of_injective _ inj] at d
  exact d

end D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit
