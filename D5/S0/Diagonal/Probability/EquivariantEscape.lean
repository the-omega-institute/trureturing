/- GID: D5/S0/Diagonal/Probability/EquivariantEscape
   generality: G
   mirror-B: D5/B/S0/Diagonal/Probability/EquivariantEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform equivariant listings have the exact transitive escape probability. -/

import D5.S0.Diagonal.EquivariantEscape
import Mathlib.Probability.Distributions.Uniform

open scoped BigOperators ENNReal

universe u v w

namespace D5.S0.Diagonal.Probability.EquivariantEscape

open D5.S0.Diagonal
open Diagonal.EscapeCount Diagonal.EquivariantEscape

variable {G : Type u} {A : Type v} {Y : Type w}

private noncomputable def orbitRepresentativeTransport [Group G] [MulAction G A]
    (a : A) : G :=
  let i : OrbitIndex G A := Quotient.mk'' a
  let hrel : (MulAction.orbitRel G A) i.out a :=
    Quotient.eq''.mp (Quotient.out_eq' i)
  let hmem : i.out ∈ MulAction.orbit G a := hrel
  ((MulAction.mem_orbit_iff.mp hmem).choose)⁻¹

private theorem orbitRepresentativeTransport_spec [Group G] [MulAction G A]
    (a : A) :
    orbitRepresentativeTransport (G := G) a •
        (Quotient.mk'' a : OrbitIndex G A).out = a := by
  rw [orbitRepresentativeTransport]
  exact inv_smul_eq_iff.mpr (MulAction.mem_orbit_iff.mp
    (show (Quotient.mk'' a : OrbitIndex G A).out ∈ MulAction.orbit G a from
      Quotient.eq''.mp (Quotient.out_eq' (Quotient.mk'' a : OrbitIndex G A)))).choose_spec.symm

private noncomputable def fullOrbitRow [Group G] [MulAction G A]
    (p : OrbitParameters (G := G) (A := A) Y) (i : OrbitIndex G A)
    (b : StabilizerOrbit G A i) : Y :=
  if h : b = diagonalOrbit i then (p i).1 else (p i).2 ⟨b, h⟩

private noncomputable def invariantRowAtOrbit [Group G] [MulAction G A]
    (g : EquivariantListing G A Y) (i : OrbitIndex G A)
    (b : StabilizerOrbit G A i) : Y :=
  Quotient.liftOn' b (fun a => g.1 i.out a) fun a c hac => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hac
    obtain ⟨σ, rfl⟩ := hac
    have hfix : (σ : G) • i.out = i.out :=
      MulAction.mem_stabilizer_iff.mp σ.property
    simpa [hfix, Subgroup.smul_def] using g.2 (σ : G) i.out c

private noncomputable def listingToParameters [Group G] [MulAction G A]
    (g : EquivariantListing G A Y) : OrbitParameters (G := G) (A := A) Y :=
  fun i =>
    ⟨g.1 i.out i.out, fun b =>
      invariantRowAtOrbit g i b.1⟩

private theorem fullOrbitRow_listingToParameters [Group G] [MulAction G A]
    (g : EquivariantListing G A Y) (i : OrbitIndex G A)
    (b : StabilizerOrbit G A i) :
    fullOrbitRow (listingToParameters g) i b = invariantRowAtOrbit g i b := by
  by_cases h : b = diagonalOrbit i
  · subst b
    simp [fullOrbitRow, listingToParameters, invariantRowAtOrbit, diagonalOrbit]
  · simp [fullOrbitRow, listingToParameters, h]

private noncomputable def parametersToListingFunction [Group G] [MulAction G A]
    (p : OrbitParameters (G := G) (A := A) Y) (a b : A) : Y :=
  let i : OrbitIndex G A := Quotient.mk'' a
  fullOrbitRow p i
    (Quotient.mk'' ((orbitRepresentativeTransport (G := G) a)⁻¹ • b))

private noncomputable def parametersToListing [Group G] [MulAction G A]
    (p : OrbitParameters (G := G) (A := A) Y) : EquivariantListing G A Y :=
  ⟨parametersToListingFunction p, by
    intro σ a b
    rw [parametersToListingFunction, parametersToListingFunction]
    have hOrbit : (Quotient.mk'' (σ • a) : OrbitIndex G A) =
        (Quotient.mk'' a : OrbitIndex G A) :=
      Quotient.sound' (MulAction.mem_orbit a σ)
    rw [hOrbit]
    apply congrArg (fullOrbitRow p (Quotient.mk'' a))
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    let τa := orbitRepresentativeTransport (G := G) a
    let τσa := orbitRepresentativeTransport (G := G) (σ • a)
    let h : MulAction.stabilizer G (Quotient.mk'' a : OrbitIndex G A).out :=
      ⟨τσa⁻¹ * σ * τa, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul]
        change τσa⁻¹ • σ •
          (orbitRepresentativeTransport (G := G) a •
            (Quotient.mk'' a : OrbitIndex G A).out) = _
        rw [orbitRepresentativeTransport_spec]
        have hτσ := orbitRepresentativeTransport_spec (G := G) (σ • a)
        rw [hOrbit] at hτσ
        exact inv_smul_eq_iff.mpr hτσ.symm⟩
    refine ⟨h, ?_⟩
    simp only [Subgroup.smul_def, h, τa, τσa, mul_smul]
    simp⟩

private theorem parametersToListing_at_out [Group G] [MulAction G A]
    (p : OrbitParameters (G := G) (A := A) Y) (i : OrbitIndex G A) (b : A) :
    parametersToListingFunction p i.out b =
      fullOrbitRow p i (Quotient.mk'' b) := by
  rw [parametersToListingFunction]
  have hi : (Quotient.mk'' i.out : OrbitIndex G A) = i := Quotient.out_eq' i
  rw [hi]
  apply congrArg (fullOrbitRow p i)
  apply Quotient.sound'
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  let τ := orbitRepresentativeTransport (G := G) i.out
  have hτ : τ • i.out = i.out := by
    have hs := orbitRepresentativeTransport_spec (G := G) i.out
    rw [hi] at hs
    exact hs
  have hτinv : τ⁻¹ • i.out = i.out := inv_smul_eq_iff.mpr hτ.symm
  exact ⟨⟨τ⁻¹, MulAction.mem_stabilizer_iff.mpr hτinv⟩, rfl⟩

private theorem parameters_listing_left_inv [Group G] [MulAction G A]
    (g : EquivariantListing G A Y) :
    parametersToListing (listingToParameters g) = g := by
  apply Subtype.ext
  funext a b
  change parametersToListingFunction (listingToParameters g) a b = g.1 a b
  rw [parametersToListingFunction,
    fullOrbitRow_listingToParameters, invariantRowAtOrbit]
  let τ := orbitRepresentativeTransport (G := G) a
  have heq := g.2 τ (Quotient.mk'' a : OrbitIndex G A).out (τ⁻¹ • b)
  simpa [τ, orbitRepresentativeTransport_spec] using heq.symm

private theorem parameters_listing_right_inv [Group G] [MulAction G A]
    (p : OrbitParameters (G := G) (A := A) Y) :
    listingToParameters (parametersToListing p) = p := by
  funext i
  apply Prod.ext
  · change parametersToListingFunction p i.out i.out = (p i).1
    rw [parametersToListing_at_out]
    simp [fullOrbitRow, diagonalOrbit]
  · funext b
    rcases b with ⟨q, hq⟩
    induction q using Quotient.inductionOn' with
    | _ c =>
      change invariantRowAtOrbit (parametersToListing p) i (Quotient.mk'' c) =
        (p i).2 ⟨Quotient.mk'' c, hq⟩
      simp only [invariantRowAtOrbit, Quotient.liftOn'_mk'']
      change parametersToListingFunction p i.out c = (p i).2 ⟨Quotient.mk'' c, hq⟩
      rw [parametersToListing_at_out]
      simp [fullOrbitRow, hq]

private abbrev CapturedAt [Group G] [MulAction G A]
    (f : Y → Y) (g : EquivariantListing G A Y) (a : A) : Prop :=
  g.1 a = diagonal f g.1

private abbrev ParameterCaptured [Group G] [MulAction G A]
    (f : Y → Y) (p : OrbitParameters (G := G) (A := A) Y)
    (i : OrbitIndex G A) : Prop :=
  f (p i).1 = (p i).1 ∧
    (p i).2 = fun b => f ((p (targetOrbit i b)).1)

private theorem equivariant_diagonal_out [Group G] [MulAction G A]
    (g : EquivariantListing G A Y) (a : A) :
    g.1 (Quotient.mk'' a : OrbitIndex G A).out
        (Quotient.mk'' a : OrbitIndex G A).out = g.1 a a := by
  have hmem : (Quotient.mk'' a : OrbitIndex G A).out ∈ MulAction.orbit G a :=
    Quotient.eq''.mp (Quotient.out_eq' (Quotient.mk'' a : OrbitIndex G A))
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hmem
  simpa [hσ] using g.2 σ a a

private theorem capturedAt_out_iff_parameterCaptured [Group G] [MulAction G A]
    (f : Y → Y) (g : EquivariantListing G A Y) (i : OrbitIndex G A) :
    CapturedAt f g i.out ↔ ParameterCaptured f (listingToParameters g) i := by
  constructor
  · intro hCaptured
    constructor
    · have h := congrFun hCaptured i.out
      change f (g.1 i.out i.out) = g.1 i.out i.out
      simpa [diagonal] using h.symm
    · funext b
      rcases b with ⟨q, hq⟩
      induction q using Quotient.inductionOn' with
      | _ c =>
        have hc := congrFun hCaptured c
        change invariantRowAtOrbit g i (Quotient.mk'' c) =
          f ((listingToParameters g (targetOrbit i ⟨Quotient.mk'' c, hq⟩)).1)
        simp only [invariantRowAtOrbit, Quotient.liftOn'_mk'', listingToParameters,
          targetOrbit, diagonal] at hc ⊢
        simpa [equivariant_diagonal_out] using hc
  · rintro ⟨hFixed, hRows⟩
    funext c
    let q : StabilizerOrbit G A i := Quotient.mk'' c
    by_cases hDiagonal : q = diagonalOrbit i
    · have hrel : (MulAction.orbitRel (MulAction.stabilizer G i.out) A) c i.out :=
        Quotient.eq''.mp hDiagonal
      obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp
        (show c ∈ MulAction.orbit (MulAction.stabilizer G i.out) i.out from hrel)
      have hc : c = i.out := by
        calc
          c = (σ : G) • i.out := by simpa [Subgroup.smul_def] using hσ.symm
          _ = i.out := MulAction.mem_stabilizer_iff.mp σ.property
      rw [hc]
      change g.1 i.out i.out = f (g.1 i.out i.out)
      change f (g.1 i.out i.out) = g.1 i.out i.out at hFixed
      exact hFixed.symm
    · have h := congrFun hRows ⟨q, hDiagonal⟩
      change invariantRowAtOrbit g i q =
        f ((listingToParameters g (targetOrbit i ⟨q, hDiagonal⟩)).1) at h
      simp only [q, invariantRowAtOrbit, Quotient.liftOn'_mk'', listingToParameters,
        targetOrbit] at h
      simpa [diagonal, equivariant_diagonal_out] using h

private noncomputable def canonicalOrbitDecomposition [Group G] [MulAction G A] :
    OrbitDecomposition (G := G) (A := A) Y where
  parameters :=
    { toFun := listingToParameters
      invFun := parametersToListing
      left_inv := parameters_listing_left_inv
      right_inv := parameters_listing_right_inv }
  escaped_iff := by
    intro f g
    change (¬∃ a, CapturedAt f g a) ↔
      ∀ i, ¬ParameterCaptured f (listingToParameters g) i
    constructor
    · intro hEscaped i hCaptured
      exact hEscaped ⟨i.out,
        (capturedAt_out_iff_parameterCaptured f g i).mpr hCaptured⟩
    · intro hParameters
      rintro ⟨a, hCaptured⟩
      let i : OrbitIndex G A := Quotient.mk'' a
      apply hParameters i
      apply (capturedAt_out_iff_parameterCaptured f g i).mp
      let τ := orbitRepresentativeTransport (G := G) a
      funext b
      have hAtTransport := congrFun hCaptured (τ • b)
      have hEquivRow := g.2 τ i.out b
      have hDiagonal := g.2 τ b b
      have hτ : τ • i.out = a := orbitRepresentativeTransport_spec a
      rw [hτ] at hEquivRow
      rw [hEquivRow] at hAtTransport
      simp only [diagonal] at hAtTransport ⊢
      rw [hDiagonal] at hAtTransport
      exact hAtTransport

private theorem transitiveEquivariantEscapedCard [Group G] [MulAction G A]
    [Fintype A] [Fintype Y] [Nonempty A] [MulAction.IsPretransitive G A]
    (f : Y → Y) (i₀ : OrbitIndex G A) :
    Nat.card {g : EquivariantListing G A Y // IsEscaped f g.1} =
      Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀) -
        Nat.card {y : Y // f y = y} :=
  transitive_equivariant_escaped_card
    (canonicalOrbitDecomposition (G := G) (A := A) (Y := Y)) f i₀

private theorem orbitParameterFactorCard [Group G] [MulAction G A] [Fintype A]
    [Fintype Y] (i : OrbitIndex G A) :
    Fintype.card
        (Y × ({b : StabilizerOrbit G A i // b ≠ diagonalOrbit i} → Y)) =
      Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  rw [← pow_succ']
  congr 1
  exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨diagonalOrbit i⟩)

private theorem transitiveEquivariantListingCard [Group G] [MulAction G A]
    [Fintype A] [Fintype Y] [Nonempty A] [MulAction.IsPretransitive G A]
    (i₀ : OrbitIndex G A) :
    Nat.card (EquivariantListing G A Y) =
      Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀) := by
  classical
  letI : Unique (OrbitIndex G A) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G A).mp inferInstance)
  rw [Nat.card_congr
    (canonicalOrbitDecomposition (G := G) (A := A) (Y := Y)).parameters]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_pi, Fintype.prod_unique]
  rw [Subsingleton.elim default i₀]
  exact orbitParameterFactorCard i₀

noncomputable instance equivariantListingFintype [Group G] [MulAction G A]
    [Fintype A] [Fintype Y] :
    Fintype (EquivariantListing G A Y) :=
  Fintype.ofFinite _

noncomputable instance equivariantListingNonempty [Group G] [MulAction G A]
    [Nonempty Y] : Nonempty (EquivariantListing G A Y) := by
  let y : Y := Classical.choice inferInstance
  exact ⟨⟨fun _ _ => y, by intro σ a b; rfl⟩⟩

/-- Under a transitive action, the uniform equivariant escape probability is exactly one minus
the fixed-point count divided by the number of stabilizer-orbit parameter choices. -/
theorem transitive_equivariant_escape_probability [Group G] [MulAction G A]
    [Fintype A] [Fintype Y] [Nonempty A] [Nonempty Y]
    [MulAction.IsPretransitive G A] (f : Y → Y) (i₀ : OrbitIndex G A) :
    (PMF.uniformOfFintype (EquivariantListing G A Y)).toOuterMeasure
        {g | IsEscaped f g.1} =
      1 -
        (↑(Nat.card {y : Y // f y = y}) : ℝ≥0∞) /
          (↑(Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀)) : ℝ≥0∞) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hEscapedCard :
      Fintype.card ↥({g | IsEscaped f g.1} : Set (EquivariantListing G A Y)) =
        Nat.card ↥({g | IsEscaped f g.1} : Set (EquivariantListing G A Y)) :=
    Nat.card_eq_fintype_card.symm
  have hListingCard : Fintype.card (EquivariantListing G A Y) =
      Nat.card (EquivariantListing G A Y) :=
    Nat.card_eq_fintype_card.symm
  rw [hEscapedCard, hListingCard]
  change
    (Nat.card {g : EquivariantListing G A Y // IsEscaped f g.1} : ℝ≥0∞) /
        (Nat.card (EquivariantListing G A Y) : ℝ≥0∞) = _
  rw [transitiveEquivariantEscapedCard f i₀, transitiveEquivariantListingCard i₀]
  have hn : 0 < Fintype.card Y := Fintype.card_pos
  have htotal :
      (↑(Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀)) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hn))
  rw [ENNReal.natCast_sub, ENNReal.sub_div (fun _ _ => htotal),
    ENNReal.div_self htotal (by simp)]

example : MulAction.IsPretransitive (Equiv.Perm (Fin 1)) (Fin 1) := inferInstance

example : Nonempty (OrbitIndex (Equiv.Perm (Fin 1)) (Fin 1)) :=
  ⟨Quotient.mk'' 0⟩

example : EquivariantListing (Equiv.Perm (Fin 1)) (Fin 1) Unit :=
  ⟨fun _ _ => (), by intro σ a b; rfl⟩

example : (1 : ℝ≥0∞) - 1 ≠ 1 := by simp

example :
    (PMF.uniformOfFintype
      (EquivariantListing (Equiv.Perm (Fin 1)) (Fin 1) Unit)).toOuterMeasure
        {g | IsEscaped (fun y : Unit => y) g.1} = 0 := by
  simpa using transitive_equivariant_escape_probability
    (G := Equiv.Perm (Fin 1)) (A := Fin 1) (Y := Unit)
    (fun y => y) (Quotient.mk'' 0)

#print axioms transitive_equivariant_escape_probability

end D5.S0.Diagonal.Probability.EquivariantEscape
