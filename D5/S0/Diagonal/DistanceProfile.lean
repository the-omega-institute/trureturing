/- GID: D5/S0/Diagonal/DistanceProfile
   generality: G
   mirror-B: D5/B/S0/Diagonal/DistanceProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact finite counts for diagonal Hamming-distance profiles and lower tails. -/

import D5.S0.Diagonal.EscapeCount
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

universe u v

namespace D5.S0.Diagonal.DistanceProfile

open EscapeCount

variable {A : Type u} {Y : Type v}

/-- The number of coordinates where a listing row differs from its twisted diagonal. -/
noncomputable def hammingDistance (f : Y → Y) (g : A → A → Y) (a : A) : ℕ :=
  Nat.card {b : A // g a b ≠ diagonal f g b}

/-- The explicit number of choices contributing one row at distance `j`. -/
noncomputable def rowDistanceCount [Fintype A] [Fintype Y] (f : Y → Y) (j : ℕ) : ℕ :=
  Nat.card {y : Y // f y = y} * Nat.choose (Fintype.card A - 1) j *
      (Fintype.card Y - 1) ^ j +
    if j = 0 then 0 else
      (Fintype.card Y - Nat.card {y : Y // f y = y}) *
        Nat.choose (Fintype.card A - 1) (j - 1) * (Fintype.card Y - 1) ^ (j - 1)

private abbrev RowParameters (A : Type u) (Y : Type v) :=
  (a : A) → Y × ({b : A // b ≠ a} → Y)

private abbrev Rows (A : Type u) (Y : Type v) :=
  (a : A) → {b : A // b ≠ a} → Y

private def rowEquiv [DecidableEq A] (a : A) :
    (A → Y) ≃ Y × ({b : A // b ≠ a} → Y) :=
  ((Equiv.optionSubtypeNe a).symm.arrowCongr (Equiv.refl Y)).trans
    Equiv.piOptionEquivProd

private def listingEquiv [DecidableEq A] :
    (A → A → Y) ≃ RowParameters A Y :=
  Equiv.piCongrRight rowEquiv

private def rowParametersEquiv :
    RowParameters A Y ≃ (A → Y) × Rows A Y where
  toFun p := ⟨fun a => (p a).1, fun a => (p a).2⟩
  invFun p a := ⟨p.1 a, p.2 a⟩
  left_inv p := by
    funext a
    rfl
  right_inv p := rfl

@[simp] private theorem listingEquiv_apply_fst [DecidableEq A] (g : A → A → Y) (a : A) :
    (listingEquiv g a).1 = g a a := by
  rfl

@[simp] private theorem listingEquiv_apply_snd [DecidableEq A] (g : A → A → Y) (a : A)
    (b : {b : A // b ≠ a}) : (listingEquiv g a).2 b = g a b := by
  rfl

@[simp] private theorem listingEquiv_symm_diag [DecidableEq A] (p : RowParameters A Y) (a : A) :
    listingEquiv.symm p a a = (p a).1 := by
  simp [listingEquiv, rowEquiv, Equiv.piCongrRight, Equiv.arrowCongr,
    Equiv.piOptionEquivProd]

@[simp] private theorem listingEquiv_symm_off [DecidableEq A] (p : RowParameters A Y) (a : A)
    (b : {b : A // b ≠ a}) : listingEquiv.symm p a b = (p a).2 b := by
  simp [listingEquiv, rowEquiv, Equiv.piCongrRight, Equiv.arrowCongr,
    Equiv.piOptionEquivProd, b.property]

private noncomputable def disagreements [Fintype A] (t h : A → Y) : Finset A := by
  classical
  exact Finset.univ.filter fun a => h a ≠ t a

private noncomputable def assemble [Fintype A] (t : A → Y) (s : Finset A)
    (q : (a : {a : A // a ∈ s}) → {y : Y // y ≠ t a.1}) : A → Y := by
  classical
  exact fun a => if ha : a ∈ s then (q ⟨a, ha⟩).1 else t a

private theorem disagreements_assemble [Fintype A] (t : A → Y) (s : Finset A)
    (q : (a : {a : A // a ∈ s}) → {y : Y // y ≠ t a.1}) :
    disagreements t (assemble t s q) = s := by
  classical
  ext a
  by_cases ha : a ∈ s
  · simp [disagreements, assemble, ha, (q ⟨a, ha⟩).property]
  · simp [disagreements, assemble, ha]

private noncomputable def supportFiberEquiv [Fintype A] (t : A → Y) (s : Finset A) :
    {h : A → Y // disagreements t h = s} ≃
      ((a : {a : A // a ∈ s}) → {y : Y // y ≠ t a.1}) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h a
    have ha : a.1 ∈ disagreements t h.1 := by
      rw [h.property]
      exact a.property
    exact ⟨h.1 a, (Finset.mem_filter.mp ha).2⟩
  · exact fun q => ⟨assemble t s q, disagreements_assemble t s q⟩
  · intro h
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ s
    · simp [assemble, ha]
    · have hnot : a ∉ disagreements t h := by simpa [h.property] using ha
      have heq : h.1 a = t a := by simpa [disagreements] using hnot
      simp [assemble, ha, heq]
  · intro q
    funext a
    apply Subtype.ext
    simp [assemble, a.property]

private noncomputable def sphereFiberEquiv [Fintype A] (t : A → Y) (j : ℕ) :
    {h : A → Y // (disagreements t h).card = j} ≃
      Σ s : {s : Finset A // s.card = j}, {h : A → Y // disagreements t h = s.1} := by
  let e : (A → Y) ≃ Σ s : Finset A, {h : A → Y // disagreements t h = s} :=
    (Equiv.sigmaFiberEquiv fun h : A → Y => disagreements t h).symm
  exact (e.subtypeEquiv fun _ => Iff.rfl).trans
    (Equiv.subtypeSigmaEquiv (fun s : Finset A => {h : A → Y // disagreements t h = s})
      fun s => s.card = j)

private noncomputable def sphereEquiv [Fintype A] (t : A → Y) (j : ℕ) :
    {h : A → Y // (disagreements t h).card = j} ≃
      Σ s : {s : Finset A // s.card = j},
        (a : {a : A // a ∈ s.1}) → {y : Y // y ≠ t a.1} :=
  (sphereFiberEquiv t j).trans (Equiv.sigmaCongrRight fun s => supportFiberEquiv t s.1)

private theorem sphere_card [Fintype A] [Fintype Y] (t : A → Y) (j : ℕ) :
    Nat.card {h : A → Y // (disagreements t h).card = j} =
      Nat.choose (Fintype.card A) j * (Fintype.card Y - 1) ^ j := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (sphereEquiv t j), Fintype.card_sigma]
  calc
    (∑ s : {s : Finset A // s.card = j},
        Fintype.card ((a : {a : A // a ∈ s.1}) → {y : Y // y ≠ t a.1})) =
        ∑ _s : {s : Finset A // s.card = j}, (Fintype.card Y - 1) ^ j := by
      apply Fintype.sum_congr
      intro s
      simp [Fintype.card_pi, Fintype.card_subtype_compl, s.property]
    _ = _ := by simp [Fintype.card_finset_len]

private theorem hammingDistance_listingEquiv [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (p : RowParameters A Y) (a : A) :
    hammingDistance f (listingEquiv.symm p) a =
      (if f (p a).1 = (p a).1 then 0 else 1) +
        (disagreements (fun b : {b : A // b ≠ a} => f (p b.1).1) (p a).2).card := by
  classical
  let target : {b : A // b ≠ a} → Y := fun b => f (p b.1).1
  have hdisagreements : (disagreements target (p a).2).card =
      ∑ b : {b : A // b ≠ a}, if (p a).2 b ≠ target b then 1 else 0 := by
    rw [disagreements]
    simpa using Finset.card_eq_sum_ite
      (s := (Finset.univ.filter fun b => (p a).2 b ≠ target b))
      (t := Finset.univ) (Finset.filter_subset _ _)
  rw [hammingDistance, Nat.card_eq_fintype_card]
  rw [Fintype.card_of_subtype
    ((Finset.univ : Finset A).filter fun b =>
      listingEquiv.symm p a b ≠ diagonal f (listingEquiv.symm p) b) (by simp)]
  calc
    ((Finset.univ : Finset A).filter fun b =>
          listingEquiv.symm p a b ≠ diagonal f (listingEquiv.symm p) b).card =
        ∑ b : A, if listingEquiv.symm p a b ≠ diagonal f (listingEquiv.symm p) b
          then 1 else 0 := by
      simpa using Finset.card_eq_sum_ite
        (s := ((Finset.univ : Finset A).filter fun b =>
          listingEquiv.symm p a b ≠ diagonal f (listingEquiv.symm p) b))
        (t := Finset.univ) (Finset.filter_subset _ _)
    _ = ∑ b : Option {b : A // b ≠ a},
        if listingEquiv.symm p a (Equiv.optionSubtypeNe a b) ≠
          diagonal f (listingEquiv.symm p) (Equiv.optionSubtypeNe a b) then 1 else 0 :=
      ((Equiv.optionSubtypeNe a).sum_comp _).symm
    _ = (if listingEquiv.symm p a a ≠ diagonal f (listingEquiv.symm p) a then 1 else 0) +
        ∑ b : {b : A // b ≠ a},
          if listingEquiv.symm p a b ≠ diagonal f (listingEquiv.symm p) b then 1 else 0 := by
      rw [Fintype.sum_option]
      simp only [Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some]
      rfl
    _ = _ := by
      rw [hdisagreements]
      by_cases h : f (p a).1 = (p a).1
      · simp [target, diagonal, h]
      · have h' : (p a).1 ≠ f (p a).1 := fun h' => h h'.symm
        simp [target, diagonal, h, h']

private noncomputable abbrev RowDistanceValue [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (X : A → Y) (a : A) (q : {b : A // b ≠ a} → Y) : ℕ :=
  (if f (X a) = X a then 0 else 1) +
    (disagreements (fun b : {b : A // b ≠ a} => f (X b.1)) q).card

private abbrev RowDistancePredicate [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (X : A → Y) (a : A)
    (j : ℕ) (q : {b : A // b ≠ a} → Y) : Prop :=
  RowDistanceValue f X a q = j

private theorem rowDistanceValue_le [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (X : A → Y) (a : A) (q : {b : A // b ≠ a} → Y) :
    RowDistanceValue f X a q ≤ Fintype.card A := by
  have hOffCard : Fintype.card {b : A // b ≠ a} = Fintype.card A - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  let d := (disagreements (fun b : {b : A // b ≠ a} => f (X b.1)) q).card
  have hOff : d ≤ Fintype.card A - 1 := by
    simpa [d, hOffCard] using
      (disagreements (fun b : {b : A // b ≠ a} => f (X b.1)) q).card_le_univ
  have hA : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨a⟩
  change (if f (X a) = X a then 0 else 1) + d ≤ Fintype.card A
  by_cases hFixed : f (X a) = X a
  · rw [if_pos hFixed, zero_add]
    omega
  · rw [if_neg hFixed]
    omega

private theorem rowFiber_card [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (X : A → Y)
    (a : A) (j : ℕ) :
    Fintype.card {q : {b : A // b ≠ a} → Y // RowDistancePredicate f X a j q} =
      if f (X a) = X a then
        Nat.choose (Fintype.card A - 1) j * (Fintype.card Y - 1) ^ j
      else if j = 0 then 0 else
        Nat.choose (Fintype.card A - 1) (j - 1) *
          (Fintype.card Y - 1) ^ (j - 1) := by
  classical
  let target : {b : A // b ≠ a} → Y := fun b => f (X b.1)
  have hOffCard : Fintype.card {b : A // b ≠ a} = Fintype.card A - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  by_cases hFixed : f (X a) = X a
  · simp only [RowDistancePredicate, RowDistanceValue, if_pos hFixed, zero_add]
    simpa [target, hOffCard, Nat.card_eq_fintype_card] using sphere_card target j
  · simp only [RowDistancePredicate, RowDistanceValue, if_neg hFixed]
    by_cases hj : j = 0
    · subst j
      simp
    · have hjPos : 0 < j := Nat.pos_of_ne_zero hj
      calc
        Fintype.card
            {q : {b : A // b ≠ a} → Y //
              1 + (disagreements target q).card = j} =
            Fintype.card
              {q : {b : A // b ≠ a} → Y //
                (disagreements target q).card = j - 1} := by
          apply Fintype.card_congr
          apply (Equiv.refl ({b : A // b ≠ a} → Y)).subtypeEquiv
          intro q
          change 1 + (disagreements target q).card = j ↔
            (disagreements target q).card = j - 1
          omega
        _ = _ := by
          simpa [target, hOffCard, Nat.card_eq_fintype_card, hj] using
            sphere_card target (j - 1)

private noncomputable def rowTailEquiv [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (X : A → Y) (a : A) (r : ℕ) :
    {q : {b : A // b ≠ a} → Y // r ≤ RowDistanceValue f X a q} ≃
      Σ j : {j : ℕ // j ∈ Finset.Icc r (Fintype.card A)},
        {q : {b : A // b ≠ a} → Y // RowDistancePredicate f X a j.1 q} where
  toFun q :=
    ⟨⟨RowDistanceValue f X a q.1,
      Finset.mem_Icc.mpr ⟨q.2, rowDistanceValue_le f X a q.1⟩⟩, ⟨q.1, rfl⟩⟩
  invFun p := ⟨p.2.1, by
    rw [p.2.2]
    exact (Finset.mem_Icc.mp p.1.2).1⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨⟨j, hj⟩, ⟨q, hq⟩⟩
    dsimp at hq ⊢
    subst j
    rfl

private theorem rowTailFiber_card [Fintype A] [Fintype Y] [DecidableEq A]
    [DecidableEq Y] (f : Y → Y) (X : A → Y) (a : A) (r : ℕ) :
    Fintype.card
        {q : {b : A // b ≠ a} → Y // r ≤ RowDistanceValue f X a q} =
      ∑ j ∈ Finset.Icc r (Fintype.card A),
        if f (X a) = X a then
          Nat.choose (Fintype.card A - 1) j * (Fintype.card Y - 1) ^ j
        else if j = 0 then 0 else
          Nat.choose (Fintype.card A - 1) (j - 1) *
            (Fintype.card Y - 1) ^ (j - 1) := by
  classical
  rw [Fintype.card_congr (rowTailEquiv f X a r), Fintype.card_sigma]
  rw [← Finset.sum_subtype (p := fun j : ℕ => j ∈ Finset.Icc r (Fintype.card A))
    (Finset.Icc r (Fintype.card A)) (by simp)
    (fun j => Fintype.card
      {q : {b : A // b ≠ a} → Y // RowDistancePredicate f X a j q})]
  apply Finset.sum_congr rfl
  intro j hj
  exact rowFiber_card f X a j

private abbrev ProfileParameters [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (r : A → ℕ) :=
  Σ X : A → Y,
    (a : A) →
      {q : {b : A // b ≠ a} → Y // RowDistancePredicate f X a (r a) q}

private noncomputable def profileEquiv [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (r : A → ℕ) :
    {g : A → A → Y // ∀ a, hammingDistance f g a = r a} ≃
      ProfileParameters (A := A) (Y := Y) f r := by
  let e : (A → A → Y) ≃ (A → Y) × Rows A Y :=
    listingEquiv.trans rowParametersEquiv
  let eProfile :
      {g : A → A → Y // ∀ a, hammingDistance f g a = r a} ≃
        {p : (A → Y) × Rows A Y //
          ∀ a, RowDistancePredicate f p.1 a (r a) (p.2 a)} :=
    e.subtypeEquiv fun g => by
      constructor
      · intro hg a
        change
          (if f (listingEquiv g a).1 = (listingEquiv g a).1 then 0 else 1) +
              (disagreements
                (fun b : {b : A // b ≠ a} => f (listingEquiv g b.1).1)
                (listingEquiv g a).2).card = r a
        rw [← hammingDistance_listingEquiv f (listingEquiv g) a]
        simpa using hg a
      · intro hp a
        have ha := hp a
        change
          (if f (listingEquiv g a).1 = (listingEquiv g a).1 then 0 else 1) +
              (disagreements
                (fun b : {b : A // b ≠ a} => f (listingEquiv g b.1).1)
                (listingEquiv g a).2).card = r a at ha
        rw [← hammingDistance_listingEquiv f (listingEquiv g) a] at ha
        simpa using ha
  exact eProfile.trans
    ((Equiv.subtypeProdEquivSigmaSubtype fun (X : A → Y) (R : Rows A Y) =>
      ∀ a, RowDistancePredicate f X a (r a) (R a)).trans
      (Equiv.sigmaCongrRight fun _X => Equiv.subtypePiEquivPi))

private abbrev TailParameters [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (r : ℕ) :=
  Σ X : A → Y,
    (a : A) → {q : {b : A // b ≠ a} → Y // r ≤ RowDistanceValue f X a q}

private noncomputable def tailEquiv [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (r : ℕ) :
    {g : A → A → Y // ∀ a, r ≤ hammingDistance f g a} ≃
      TailParameters (A := A) (Y := Y) f r := by
  let e : (A → A → Y) ≃ (A → Y) × Rows A Y :=
    listingEquiv.trans rowParametersEquiv
  let eTail :
      {g : A → A → Y // ∀ a, r ≤ hammingDistance f g a} ≃
        {p : (A → Y) × Rows A Y // ∀ a, r ≤ RowDistanceValue f p.1 a (p.2 a)} :=
    e.subtypeEquiv fun g => by
      constructor
      · intro hg a
        change r ≤
          (if f (listingEquiv g a).1 = (listingEquiv g a).1 then 0 else 1) +
            (disagreements
              (fun b : {b : A // b ≠ a} => f (listingEquiv g b.1).1)
              (listingEquiv g a).2).card
        rw [← hammingDistance_listingEquiv f (listingEquiv g) a]
        simpa using hg a
      · intro hp a
        have ha := hp a
        change r ≤
          (if f (listingEquiv g a).1 = (listingEquiv g a).1 then 0 else 1) +
            (disagreements
              (fun b : {b : A // b ≠ a} => f (listingEquiv g b.1).1)
              (listingEquiv g a).2).card at ha
        rw [← hammingDistance_listingEquiv f (listingEquiv g) a] at ha
        simpa using ha
  exact eTail.trans
    ((Equiv.subtypeProdEquivSigmaSubtype fun (X : A → Y) (R : Rows A Y) =>
      ∀ a, r ≤ RowDistanceValue f X a (R a)).trans
      (Equiv.sigmaCongrRight fun X =>
        Equiv.subtypePiEquivPi
          (p := fun a (q : {b : A // b ≠ a} → Y) => r ≤ RowDistanceValue f X a q)))

private theorem sum_rowFiber_card [Fintype A] [Fintype Y] [DecidableEq A]
    [DecidableEq Y] (f : Y → Y) (_a : A) (j : ℕ) :
    (∑ y : Y,
      if f y = y then
        Nat.choose (Fintype.card A - 1) j * (Fintype.card Y - 1) ^ j
      else if j = 0 then 0 else
        Nat.choose (Fintype.card A - 1) (j - 1) *
          (Fintype.card Y - 1) ^ (j - 1)) = rowDistanceCount (A := A) f j := by
  classical
  let fixedTerm := Nat.choose (Fintype.card A - 1) j * (Fintype.card Y - 1) ^ j
  let movingTerm := if j = 0 then 0 else
    Nat.choose (Fintype.card A - 1) (j - 1) * (Fintype.card Y - 1) ^ (j - 1)
  have hFixedCard : ((Finset.univ : Finset Y).filter fun y => f y = y).card =
      Nat.card {y : Y // f y = y} := by
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype (fun y : Y => f y = y)).symm
  have hMovingCard : ((Finset.univ : Finset Y).filter fun y => ¬f y = y).card =
      Fintype.card Y - Nat.card {y : Y // f y = y} := by
    calc
      ((Finset.univ : Finset Y).filter fun y => ¬f y = y).card =
          Fintype.card {y : Y // ¬f y = y} := by
        simpa using (Fintype.card_subtype (fun y : Y => ¬f y = y)).symm
      _ = Fintype.card Y - Fintype.card {y : Y // f y = y} :=
        Fintype.card_subtype_compl (fun y : Y => f y = y)
      _ = _ := by rw [Nat.card_eq_fintype_card]
  calc
    (∑ y : Y, if f y = y then fixedTerm else movingTerm) =
        ∑ y ∈ (Finset.univ.filter fun y : Y => f y = y), fixedTerm +
          ∑ y ∈ (Finset.univ.filter fun y : Y => ¬f y = y), movingTerm := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun y : Y => f y = y)]
      apply congrArg₂ (.+.)
      · apply Finset.sum_congr rfl
        intro y hy
        rw [if_pos (Finset.mem_filter.mp hy).2]
      · apply Finset.sum_congr rfl
        intro y hy
        rw [if_neg (Finset.mem_filter.mp hy).2]
    _ = Nat.card {y : Y // f y = y} * fixedTerm +
        (Fintype.card Y - Nat.card {y : Y // f y = y}) * movingTerm := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, hFixedCard, hMovingCard]
    _ = rowDistanceCount (A := A) f j := by
      simp [rowDistanceCount, fixedTerm, movingTerm, mul_assoc]

/-- Exact diagonal-distance profiles factor into the product of their row counts. -/
theorem distance_profile_card [Fintype A] [Fintype Y] (f : Y → Y) (r : A → ℕ) :
    Nat.card {g : A → A → Y // ∀ a, hammingDistance f g a = r a} =
      ∏ a, rowDistanceCount (A := A) f (r a) := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {g : A → A → Y // ∀ a, hammingDistance f g a = r a} =
        Fintype.card (ProfileParameters f r) :=
      Fintype.card_congr (profileEquiv f r)
    _ = ∑ X : A → Y,
        Fintype.card ((a : A) →
          {q : {b : A // b ≠ a} → Y // RowDistancePredicate f X a (r a) q}) :=
      Fintype.card_sigma
    _ = ∑ X : A → Y, ∏ a,
        Fintype.card
          {q : {b : A // b ≠ a} → Y // RowDistancePredicate f X a (r a) q} := by
      apply Finset.sum_congr rfl
      intro X _
      exact Fintype.card_pi
    _ = ∑ X : A → Y, ∏ a,
        if f (X a) = X a then
          Nat.choose (Fintype.card A - 1) (r a) * (Fintype.card Y - 1) ^ (r a)
        else if r a = 0 then 0 else
          Nat.choose (Fintype.card A - 1) (r a - 1) *
            (Fintype.card Y - 1) ^ (r a - 1) := by
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.prod_congr rfl
      intro a _
      exact rowFiber_card f X a (r a)
    _ = ∏ a, ∑ y : Y,
        if f y = y then
          Nat.choose (Fintype.card A - 1) (r a) * (Fintype.card Y - 1) ^ (r a)
        else if r a = 0 then 0 else
          Nat.choose (Fintype.card A - 1) (r a - 1) *
            (Fintype.card Y - 1) ^ (r a - 1) := by
      symm
      exact Fintype.prod_sum fun (a : A) (y : Y) =>
        if f y = y then
          Nat.choose (Fintype.card A - 1) (r a) * (Fintype.card Y - 1) ^ (r a)
        else if r a = 0 then 0 else
          Nat.choose (Fintype.card A - 1) (r a - 1) *
            (Fintype.card Y - 1) ^ (r a - 1)
    _ = _ := Finset.prod_congr rfl fun a _ => sum_rowFiber_card f a (r a)

/-- A listing is escaped exactly when every row has positive diagonal distance. -/
theorem isEscaped_iff_one_le_distance [Fintype A] (f : Y → Y) (g : A → A → Y) :
    IsEscaped f g ↔ ∀ a, 1 ≤ hammingDistance f g a := by
  classical
  constructor
  · intro hEscaped a
    rw [hammingDistance, Nat.card_eq_fintype_card]
    apply Fintype.card_pos_iff.mpr
    by_contra hEmpty
    apply hEscaped
    refine ⟨a, ?_⟩
    funext b
    by_contra hne
    exact hEmpty ⟨⟨b, hne⟩⟩
  · intro hDistance hRange
    rcases hRange with ⟨a, ha⟩
    have hNonempty := hDistance a
    rw [hammingDistance, Nat.card_eq_fintype_card] at hNonempty
    rcases Fintype.card_pos_iff.mp hNonempty with ⟨⟨b, hb⟩⟩
    exact hb (congrFun ha b)

/-- The number of listings whose row distances share a lower bound is a row-tail power. -/
theorem min_distance_tail [Fintype A] [Fintype Y] (f : Y → Y) (r : ℕ) :
    Nat.card {g : A → A → Y // ∀ a, r ≤ hammingDistance f g a} =
      (∑ j ∈ Finset.Icc r (Fintype.card A), rowDistanceCount (A := A) f j) ^
        Fintype.card A := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {g : A → A → Y // ∀ a, r ≤ hammingDistance f g a} =
        Fintype.card (TailParameters f r) := Fintype.card_congr (tailEquiv f r)
    _ = ∑ X : A → Y,
        Fintype.card ((a : A) →
          {q : {b : A // b ≠ a} → Y // r ≤ RowDistanceValue f X a q}) :=
      Fintype.card_sigma
    _ = ∑ X : A → Y, ∏ a,
        Fintype.card
          {q : {b : A // b ≠ a} → Y // r ≤ RowDistanceValue f X a q} := by
      apply Finset.sum_congr rfl
      intro X _
      exact Fintype.card_pi
    _ = ∑ X : A → Y, ∏ a,
        ∑ j ∈ Finset.Icc r (Fintype.card A),
          if f (X a) = X a then
            Nat.choose (Fintype.card A - 1) j * (Fintype.card Y - 1) ^ j
          else if j = 0 then 0 else
            Nat.choose (Fintype.card A - 1) (j - 1) *
              (Fintype.card Y - 1) ^ (j - 1) := by
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.prod_congr rfl
      intro a _
      exact rowTailFiber_card f X a r
    _ = ∏ a, ∑ y : Y,
        ∑ j ∈ Finset.Icc r (Fintype.card A),
          if f y = y then
            Nat.choose (Fintype.card A - 1) j * (Fintype.card Y - 1) ^ j
          else if j = 0 then 0 else
            Nat.choose (Fintype.card A - 1) (j - 1) *
              (Fintype.card Y - 1) ^ (j - 1) := by
      symm
      exact Fintype.prod_sum fun (a : A) (y : Y) =>
        ∑ j ∈ Finset.Icc r (Fintype.card A),
          if f y = y then
            Nat.choose (Fintype.card A - 1) j * (Fintype.card Y - 1) ^ j
          else if j = 0 then 0 else
            Nat.choose (Fintype.card A - 1) (j - 1) *
              (Fintype.card Y - 1) ^ (j - 1)
    _ = ∏ _a : A,
        ∑ j ∈ Finset.Icc r (Fintype.card A), rowDistanceCount (A := A) f j := by
      apply Finset.prod_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact sum_rowFiber_card f a j
    _ = _ := Finset.prod_const _

/-- Positive distance in every row specializes the tail count to the frozen escape formula. -/
theorem min_distance_one [Fintype A] [Fintype Y] (f : Y → Y) :
    Nat.card {g : A → A → Y // ∀ a, 1 ≤ hammingDistance f g a} =
      (Fintype.card Y ^ Fintype.card A - Nat.card {y : Y // f y = y}) ^
        Fintype.card A := by
  classical
  let e : {g : A → A → Y // ∀ a, 1 ≤ hammingDistance f g a} ≃
      {g : A → A → Y // IsEscaped f g} :=
    (Equiv.refl (A → A → Y)).subtypeEquiv fun g =>
      (isEscaped_iff_one_le_distance f g).symm
  rw [min_distance_tail]
  calc
    (∑ j ∈ Finset.Icc 1 (Fintype.card A), rowDistanceCount (A := A) f j) ^
          Fintype.card A =
        Nat.card {g : A → A → Y // ∀ a, 1 ≤ hammingDistance f g a} :=
      (min_distance_tail (A := A) f 1).symm
    _ = Nat.card {g : A → A → Y // IsEscaped f g} := Nat.card_congr e
    _ = _ := escaped_listing_card f

end D5.S0.Diagonal.DistanceProfile
