/- GID: D5/S0/Diagonal/CaptureCount
   generality: G
   mirror-B: D5/B/S0/Diagonal/CaptureCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Simultaneous diagonal captures have an exact finite count and factor independently. -/

import D5.S0.Diagonal.EscapeCount

universe u v

namespace D5.S0.Diagonal.CaptureCount

open EscapeCount

variable {A : Type u} {Y : Type v}

private abbrev CapturedRows (S : Finset A) := {a : A // a ∈ S}

private abbrev FreeRows (S : Finset A) := {a : A // a ∉ S}

private abbrev CaptureParameters (f : Y → Y) (S : Finset A) :=
  (CapturedRows S → {y : Y // f y = y}) × (FreeRows S → A → Y)

private def parameterDiagonal [DecidableEq A] (f : Y → Y) (S : Finset A)
    (p : CaptureParameters f S) : A → Y := fun a =>
  if ha : a ∈ S then p.1 ⟨a, ha⟩ else f (p.2 ⟨a, ha⟩ a)

private def listingOfParameters [DecidableEq A] (f : Y → Y) (S : Finset A)
    (p : CaptureParameters f S) : A → A → Y := fun a =>
  if ha : a ∈ S then parameterDiagonal f S p else p.2 ⟨a, ha⟩

private theorem listingOfParameters_capture [DecidableEq A] (f : Y → Y) (S : Finset A)
    (p : CaptureParameters f S) :
    ∀ a ∈ S, listingOfParameters f S p a = diagonal f (listingOfParameters f S p) := by
  intro a ha
  funext b
  by_cases hb : b ∈ S
  · simp [listingOfParameters, parameterDiagonal, diagonal, ha, hb, (p.1 ⟨b, hb⟩).property]
  · simp [listingOfParameters, parameterDiagonal, diagonal, ha, hb]

private def parametersOfCapture [DecidableEq A] (f : Y → Y) (S : Finset A)
    (g : {g : A → A → Y // ∀ a ∈ S, g a = diagonal f g}) : CaptureParameters f S :=
  ⟨fun a => ⟨g.1 a a, diagonal_landing_fixed (g.2 a a.property)⟩, fun a => g.1 a⟩

private def captureEquiv [DecidableEq A] (f : Y → Y) (S : Finset A) :
    CaptureParameters f S ≃ {g : A → A → Y // ∀ a ∈ S, g a = diagonal f g} where
  toFun p := ⟨listingOfParameters f S p, listingOfParameters_capture f S p⟩
  invFun := parametersOfCapture f S
  left_inv p := by
    apply Prod.ext
    · funext a
      apply Subtype.ext
      simp [parametersOfCapture, listingOfParameters, parameterDiagonal]
    · funext a
      simp [parametersOfCapture, listingOfParameters, a.property]
  right_inv g := by
    apply Subtype.ext
    funext a b
    change listingOfParameters f S (parametersOfCapture f S g) a b = g.1 a b
    by_cases ha : a ∈ S
    · rw [listingOfParameters, dif_pos ha]
      rw [congrFun (g.2 a ha) b]
      by_cases hb : b ∈ S
      · simp [parameterDiagonal, parametersOfCapture, diagonal, hb,
          diagonal_landing_fixed (g.2 b hb)]
      · simp [parameterDiagonal, parametersOfCapture, diagonal, hb]
    · simp [listingOfParameters, parametersOfCapture, ha]

/-- Capturing the twisted diagonal on a finite set of rows has an exact cardinality. -/
theorem capture_inter_card [Fintype A] [Fintype Y] (f : Y → Y) (S : Finset A) :
    Nat.card {g : A → A → Y // ∀ a ∈ S, g a = diagonal f g} =
      Nat.card {y : Y // f y = y} ^ S.card *
        Fintype.card Y ^ (Fintype.card A * (Fintype.card A - S.card)) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card {g : A → A → Y // ∀ a ∈ S, g a = diagonal f g} =
        Fintype.card (CaptureParameters f S) :=
      Fintype.card_congr (captureEquiv f S).symm
    _ = _ := by
      simp [CaptureParameters, CapturedRows, FreeRows, Fintype.card_prod,
        Fintype.card_pi, Fintype.card_subtype_compl, pow_mul]

/-- Finite intersections of capture events satisfy the integer form of independence. -/
theorem capture_independent [Fintype A] [Fintype Y] (f : Y → Y) (S : Finset A) :
    Nat.card {g : A → A → Y // ∀ a ∈ S, g a = diagonal f g} *
        (Fintype.card Y ^ (Fintype.card A ^ 2)) ^ S.card =
      (Nat.card {y : Y // f y = y} *
          Fintype.card Y ^ (Fintype.card A * (Fintype.card A - 1))) ^ S.card *
        Fintype.card Y ^ (Fintype.card A ^ 2) := by
  classical
  rw [capture_inter_card]
  have hS : S.card ≤ Fintype.card A := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hExponent :
      Fintype.card A * (Fintype.card A - S.card) + Fintype.card A ^ 2 * S.card =
        Fintype.card A * (Fintype.card A - 1) * S.card + Fintype.card A ^ 2 := by
    by_cases hA : Fintype.card A = 0
    · have hS0 : S.card = 0 := Nat.eq_zero_of_le_zero (hA ▸ hS)
      simp [hA, hS0]
    · have hA1 : 1 ≤ Fintype.card A := Nat.one_le_iff_ne_zero.mpr hA
      have hMul : Fintype.card A * S.card =
          (Fintype.card A - 1) * S.card + S.card := by
        calc
          Fintype.card A * S.card = ((Fintype.card A - 1) + 1) * S.card := by
            rw [Nat.sub_add_cancel hA1]
          _ = _ := by rw [Nat.add_mul, one_mul]
      have hInner : Fintype.card A - S.card + Fintype.card A * S.card =
          (Fintype.card A - 1) * S.card + Fintype.card A := by
        calc
          Fintype.card A - S.card + Fintype.card A * S.card =
              Fintype.card A - S.card +
                ((Fintype.card A - 1) * S.card + S.card) := by rw [hMul]
          _ = (Fintype.card A - 1) * S.card +
                (Fintype.card A - S.card + S.card) := by ac_rfl
          _ = _ := by rw [Nat.sub_add_cancel hS]
      calc
        Fintype.card A * (Fintype.card A - S.card) +
              Fintype.card A ^ 2 * S.card =
            Fintype.card A *
              (Fintype.card A - S.card + Fintype.card A * S.card) := by
          rw [Nat.mul_add, pow_two, Nat.mul_assoc]
        _ = Fintype.card A *
              ((Fintype.card A - 1) * S.card + Fintype.card A) := by rw [hInner]
        _ = _ := by rw [Nat.mul_add, Nat.mul_assoc, pow_two]
  calc
    (Nat.card {y : Y // f y = y} ^ S.card *
          Fintype.card Y ^ (Fintype.card A * (Fintype.card A - S.card))) *
        (Fintype.card Y ^ (Fintype.card A ^ 2)) ^ S.card =
        Nat.card {y : Y // f y = y} ^ S.card *
          Fintype.card Y ^
            (Fintype.card A * (Fintype.card A - S.card) +
              Fintype.card A ^ 2 * S.card) := by
      rw [← pow_mul, mul_assoc, ← pow_add]
    _ = Nat.card {y : Y // f y = y} ^ S.card *
          Fintype.card Y ^
            (Fintype.card A * (Fintype.card A - 1) * S.card +
              Fintype.card A ^ 2) := by
      rw [hExponent]
    _ = (Nat.card {y : Y // f y = y} *
          Fintype.card Y ^ (Fintype.card A * (Fintype.card A - 1))) ^ S.card *
        Fintype.card Y ^ (Fintype.card A ^ 2) := by
      rw [mul_pow, ← pow_mul, pow_add, mul_assoc]
      rw [← mul_assoc]

/-- A fixed-point-free twist escapes every finite listing in cardinality. -/
theorem escaped_card_of_fixfree [Fintype A] [Fintype Y] (f : Y → Y)
    (hfix : Nat.card {y : Y // f y = y} = 0) :
    Nat.card {g : A → A → Y // IsEscaped f g} =
      Fintype.card Y ^ (Fintype.card A ^ 2) := by
  simpa [hfix, pow_two, pow_mul] using escaped_listing_card f

/-- A fixed-point-free twist escapes every finite self-application listing. -/
theorem escape_all_of_fixfree [Fintype A] [Fintype Y] (f : Y → Y)
    (hfix : Nat.card {y : Y // f y = y} = 0) :
    ∀ g : A → A → Y, IsEscaped f g := by
  classical
  intro g
  by_contra hg
  have hEscaped := escaped_card_of_fixfree (A := A) f hfix
  have hAll : Nat.card (A → A → Y) =
      Fintype.card Y ^ (Fintype.card A ^ 2) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
    simp [pow_two, pow_mul]
  have hStrict : Nat.card {g : A → A → Y // IsEscaped f g} < Nat.card (A → A → Y) := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_lt (p := fun g : A → A → Y => IsEscaped f g) hg)
  rw [hEscaped, hAll] at hStrict
  exact (Nat.lt_irrefl _ hStrict)

end D5.S0.Diagonal.CaptureCount
