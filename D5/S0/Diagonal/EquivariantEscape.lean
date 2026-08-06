/- GID: D5/S0/Diagonal/EquivariantEscape
   generality: G
   mirror-B: D5/B/S0/Diagonal/EquivariantEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equivariant diagonal escape counts factor exactly over the action orbits. -/

import D5.S0.Diagonal.EscapeCount
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

open scoped BigOperators

universe u v w

namespace D5.S0.Diagonal.EquivariantEscape

open EscapeCount

variable {G : Type u} {A : Type v} {Y : Type w}

/-- A listing is equivariant when simultaneous transport of its row and column changes no value. -/
def IsEquivariant (G : Type u) [Group G] [MulAction G A] (g : A → A → Y) : Prop :=
  ∀ (σ : G) (a b : A), g (σ • a) (σ • b) = g a b

/-- The finite listings respecting a given group action. -/
abbrev EquivariantListing (G : Type u) (A : Type v) (Y : Type w)
    [Group G] [MulAction G A] :=
  {g : A → A → Y // IsEquivariant G g}

/-- The diagonal of an equivariant listing is constant along every action orbit. -/
theorem equivariant_diagonal_constant [Group G] [MulAction G A]
    (g : EquivariantListing G A Y) (σ : G) (a : A) :
    g.1 (σ • a) (σ • a) = g.1 a a :=
  g.2 σ a a

/-- The index type of the orbits of `A` under `G`. -/
abbrev OrbitIndex (G : Type u) (A : Type v) [Group G] [MulAction G A] :=
  MulAction.orbitRel.Quotient G A

/-- The `Stab(a_i)`-orbits in `A`, whose cardinality is the exponent `omega_i`. -/
abbrev StabilizerOrbit (G : Type u) (A : Type v) [Group G] [MulAction G A]
    (i : OrbitIndex G A) :=
  MulAction.orbitRel.Quotient (MulAction.stabilizer G i.out) A

noncomputable instance orbitIndexFintype [Group G] [MulAction G A] [Fintype A] :
    Fintype (OrbitIndex G A) :=
  Fintype.ofFinite _

noncomputable instance orbitIndexDecidableEq [Group G] [MulAction G A] :
    DecidableEq (OrbitIndex G A) :=
  Classical.decEq _

noncomputable instance stabilizerOrbitFintype [Group G] [MulAction G A] [Fintype A]
    (i : OrbitIndex G A) :
    Fintype (StabilizerOrbit G A i) :=
  Fintype.ofFinite _

noncomputable instance stabilizerOrbitDecidableEq [Group G] [MulAction G A]
    (i : OrbitIndex G A) : DecidableEq (StabilizerOrbit G A i) :=
  Classical.decEq _

/-- The stabilizer orbit containing the diagonal coordinate `(a_i, a_i)`. -/
noncomputable def diagonalOrbit [Group G] [MulAction G A]
    (i : OrbitIndex G A) : StabilizerOrbit G A i :=
  Quotient.mk'' i.out

private abbrev OffDiagonalOrbit [Group G] [MulAction G A]
    (i : OrbitIndex G A) :=
  {b : StabilizerOrbit G A i // b ≠ diagonalOrbit i}

/-- Forgetting from a stabilizer orbit to a `G`-orbit records the target orbit of a coordinate. -/
noncomputable def targetOrbit [Group G] [MulAction G A]
    (i : OrbitIndex G A) (b : OffDiagonalOrbit i) : OrbitIndex G A :=
  Quotient.liftOn' b.1 (fun a => (Quotient.mk'' a : OrbitIndex G A))
    fun _ _ h =>
      MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq' (Quotient.sound h)

private abbrev OrbitRows [Group G] [MulAction G A]
    (Y : Type w) :=
  (i : OrbitIndex G A) → OffDiagonalOrbit i → Y

/-- Diagonal values and the remaining stabilizer-orbit coordinates of every row orbit. -/
abbrev OrbitParameters [Group G] [MulAction G A] (Y : Type w) :=
  (i : OrbitIndex G A) → Y × (OffDiagonalOrbit i → Y)

private abbrev ParameterEscaped [Group G] [MulAction G A]
    (f : Y → Y) (p : OrbitParameters (G := G) (A := A) Y) : Prop :=
  ∀ i, ¬(f (p i).1 = (p i).1 ∧
    (p i).2 = fun b => f ((p (targetOrbit i b)).1))

/-- Explicit orbit coordinates for equivariant listings.

The fields are precisely the bridge absent from mathlib: a bijection to the stabilizer-orbit
coordinates, and preservation of the escape predicate. No cardinality identity is assumed. -/
structure OrbitDecomposition [Group G] [MulAction G A] (Y : Type w) where
  parameters : EquivariantListing G A Y ≃
    OrbitParameters (G := G) (A := A) Y
  escaped_iff : ∀ (f : Y → Y) (g : EquivariantListing G A Y),
    IsEscaped f g.1 ↔ ParameterEscaped f (parameters g)

private def parameterEquiv [Group G] [MulAction G A] :
    OrbitParameters (G := G) (A := A) Y ≃
      (OrbitIndex G A → Y) × OrbitRows (G := G) (A := A) Y where
  toFun p := ⟨fun i => (p i).1, fun i => (p i).2⟩
  invFun p i := ⟨p.1 i, p.2 i⟩
  left_inv p := by
    funext i
    exact Prod.eta (p i)
  right_inv _ := rfl

private abbrev EscapedRows [Group G] [MulAction G A]
    (f : Y → Y) (X : OrbitIndex G A → Y)
    (R : OrbitRows (G := G) (A := A) Y) : Prop :=
  ∀ i, ¬(f (X i) = X i ∧ R i = fun b => f (X (targetOrbit i b)))

private theorem off_diagonal_card [Group G] [MulAction G A] [Fintype A] [Fintype Y]
    (i : OrbitIndex G A) :
    Fintype.card (OffDiagonalOrbit i → Y) =
      Fintype.card Y ^ (Fintype.card (StabilizerOrbit G A i) - 1) := by
  classical
  rw [Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl]
  simp

private theorem row_choice_card [Group G] [MulAction G A] [Fintype A] [Fintype Y]
    [DecidableEq Y]
    (f : Y → Y) (X : OrbitIndex G A → Y)
    (i : OrbitIndex G A) :
    Fintype.card
        {r : OffDiagonalOrbit i → Y //
          ¬(f (X i) = X i ∧ r = fun b => f (X (targetOrbit i b)))} =
      Fintype.card Y ^ (Fintype.card (StabilizerOrbit G A i) - 1) -
        if f (X i) = X i then 1 else 0 := by
  classical
  rw [Fintype.card_subtype_compl, off_diagonal_card]
  split_ifs with hFixed
  · simp [hFixed]
  · simp [hFixed]

private theorem fiber_card [Group G] [MulAction G A] [Fintype A] [Fintype Y]
    [DecidableEq Y]
    (f : Y → Y) (X : OrbitIndex G A → Y) :
    Fintype.card {R : OrbitRows (G := G) (A := A) Y // EscapedRows f X R} =
      ∏ i, (Fintype.card Y ^
        (Fintype.card (StabilizerOrbit G A i) - 1) -
          if f (X i) = X i then 1 else 0) := by
  classical
  calc
    _ = Fintype.card
        ((i : OrbitIndex G A) →
          {r : OffDiagonalOrbit i → Y //
            ¬(f (X i) = X i ∧ r = fun b => f (X (targetOrbit i b)))}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = ∏ i, Fintype.card
        {r : OffDiagonalOrbit i → Y //
          ¬(f (X i) = X i ∧ r = fun b => f (X (targetOrbit i b)))} :=
      Fintype.card_pi
    _ = _ := Finset.prod_congr rfl fun i _ => row_choice_card f X i

private theorem sum_row_weights [Group G] [MulAction G A] [Fintype A] [Fintype Y]
    [DecidableEq Y]
    (f : Y → Y) (i : OrbitIndex G A) :
    (∑ y : Y, (Fintype.card Y ^
      (Fintype.card (StabilizerOrbit G A i) - 1) -
        if f y = y then 1 else 0)) =
      Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) -
        Fintype.card {y : Y // f y = y} := by
  classical
  have hIndicatorLe : ∀ y ∈ (Finset.univ : Finset Y),
      (if f y = y then 1 else 0) ≤ Fintype.card Y ^
        (Fintype.card (StabilizerOrbit G A i) - 1) := by
    intro y _
    split_ifs
    · exact one_le_pow₀ (Fintype.card_pos_iff.mpr ⟨y⟩)
    · exact Nat.zero_le _
  rw [Finset.sum_tsub_distrib Finset.univ hIndicatorLe]
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [Finset.sum_boole, ← Fintype.card_subtype]
  congr 1
  rw [← pow_succ']
  congr 1
  exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨diagonalOrbit i⟩)

/-- The orbit-coordinate model has the product count predicted by the stabilizer exponents. -/
theorem orbit_parameter_escaped_card [Group G] [MulAction G A] [Fintype A] [Fintype Y]
    (f : Y → Y) :
    Nat.card {p : OrbitParameters (G := G) (A := A) Y // ParameterEscaped f p} =
      ∏ i : OrbitIndex G A,
        (Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) -
          Nat.card {y : Y // f y = y}) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card {p : OrbitParameters (G := G) (A := A) Y // ParameterEscaped f p} =
        Fintype.card
          {p : (OrbitIndex G A → Y) ×
              OrbitRows (G := G) (A := A) Y // EscapedRows f p.1 p.2} := by
      apply Fintype.card_congr
      apply parameterEquiv.subtypeEquiv
      intro p
      rfl
    _ = Fintype.card
        (Σ X : OrbitIndex G A → Y,
          {R : OrbitRows (G := G) (A := A) Y // EscapedRows f X R}) :=
      Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (EscapedRows f))
    _ = ∑ X : OrbitIndex G A → Y,
        Fintype.card {R : OrbitRows (G := G) (A := A) Y // EscapedRows f X R} :=
      Fintype.card_sigma
    _ = ∑ X : OrbitIndex G A → Y, ∏ i,
        (Fintype.card Y ^
          (Fintype.card (StabilizerOrbit G A i) - 1) -
            if f (X i) = X i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro X _
      exact fiber_card f X
    _ = ∏ i : OrbitIndex G A, ∑ y : Y,
        (Fintype.card Y ^
          (Fintype.card (StabilizerOrbit G A i) - 1) -
            if f y = y then 1 else 0) := by
      symm
      exact Fintype.prod_sum fun i y =>
        Fintype.card Y ^
          (Fintype.card (StabilizerOrbit G A i) - 1) -
            if f y = y then 1 else 0
    _ = ∏ i : OrbitIndex G A,
        (Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) -
          Fintype.card {y : Y // f y = y}) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_row_weights f i

private def escapedEquiv [Group G] [MulAction G A]
    (D : OrbitDecomposition (G := G) (A := A) Y) (f : Y → Y) :
    {g : EquivariantListing G A Y // IsEscaped f g.1} ≃
      {p : OrbitParameters (G := G) (A := A) Y // ParameterEscaped f p} :=
  D.parameters.subtypeEquiv fun g => D.escaped_iff f g

/-- General equivariant escape count: one exact factor for every `G`-orbit of addresses. -/
theorem equivariant_escaped_card [Group G] [MulAction G A] [Fintype A]
    [Fintype Y] (D : OrbitDecomposition (G := G) (A := A) Y) (f : Y → Y) :
    Nat.card
        {g : EquivariantListing G A Y // IsEscaped f g.1} =
      ∏ i : OrbitIndex G A,
        (Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) -
          Nat.card {y : Y // f y = y}) := by
  rw [Nat.card_congr (escapedEquiv D f), orbit_parameter_escaped_card]

/-- For a transitive action the general product contains exactly one stabilizer-orbit factor. -/
theorem transitive_equivariant_escaped_card [Group G] [MulAction G A] [Fintype A]
    [Fintype Y] [Nonempty A] [MulAction.IsPretransitive G A]
    (D : OrbitDecomposition (G := G) (A := A) Y) (f : Y → Y) (i₀ : OrbitIndex G A) :
    Nat.card
        {g : EquivariantListing G A Y // IsEscaped f g.1} =
      Fintype.card Y ^
          Fintype.card (StabilizerOrbit G A i₀) -
        Nat.card {y : Y // f y = y} := by
  classical
  letI : Unique (OrbitIndex G A) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G A).mp inferInstance)
  rw [equivariant_escaped_card D f, Fintype.prod_unique]
  rw [Subsingleton.elim default i₀]

/-- With trivial orbit data, the product side is exactly the previously frozen free count. -/
theorem trivial_action_recovers_escaped_listing_card [Fintype A] [Fintype Y] (f : Y → Y) :
    (∏ _ : A,
        (Fintype.card Y ^ Fintype.card A - Nat.card {y : Y // f y = y})) =
      Nat.card {g : A → A → Y // IsEscaped f g} := by
  rw [escaped_listing_card]
  simp

/-- Arithmetic check for the regular three-point reading. -/
theorem regular_z3_small_case : 3 ^ 3 - 3 = 24 ∧ 3 ^ 3 = 27 := by
  decide

/-- Arithmetic check for the regular four-point reading. -/
theorem regular_z4_small_case : 2 ^ 4 - 2 = 14 ∧ 2 ^ 4 = 16 := by
  decide

/-- Arithmetic check for the nonregular transitive reading with two stabilizer orbits. -/
theorem nonregular_s3_small_case : 3 ^ 2 - 3 = 6 ∧ 3 ^ 2 = 9 := by
  decide

/-- Arithmetic check for the nontransitive two-orbit product reading. -/
theorem double_orbit_small_case :
    (2 ^ 3 - 2) * (2 ^ 2 - 2) = 12 ∧ 2 ^ 3 * 2 ^ 2 = 32 := by
  decide

end D5.S0.Diagonal.EquivariantEscape
