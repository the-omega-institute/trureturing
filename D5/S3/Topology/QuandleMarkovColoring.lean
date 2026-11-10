/- GID: D5/S3/Topology/QuandleMarkovColoring
   generality: G
   mirror-B: D5/B/S3/Topology/QuandleMarkovColoring
   mirror-E: none(waiver:algebraically-proved)
   anchors: [lake/module/Mathlib.Algebra.Quandle]
   utility: none
   digest: Signed Markov stabilizations preserve quandle coloring spaces and counts. -/

import D5.S0.Certificates.Quandles.BraidColoringTransport
import D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Rack boundary transport, Artin relations, and the untouched-strand inclusion. -/

open scoped Quandles

namespace D5.S3.Topology.QuandleMarkovColoring

open D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation

variable (Q : Type*) [Rack Q]

/-- Boundary colorings of an ordered family of strands. -/
abbrev Colors (n : ℕ) := Fin n → Q

private def leftSlot {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val, by omega⟩
private def rightSlot {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i.val + 1, by omega⟩

private theorem slots_ne {n : ℕ} (i : Fin (n - 1)) : leftSlot i ≠ rightSlot i := by
  intro h
  have := congrArg Fin.val h
  simp only [leftSlot, rightSlot] at this
  omega

private def crossing {n : ℕ} (i : Fin (n - 1)) (c : Colors Q n) : Colors Q n :=
  Function.update (Function.update c (leftSlot i) (c (leftSlot i) ◃ c (rightSlot i)))
    (rightSlot i) (c (leftSlot i))

private def inverseCrossing {n : ℕ} (i : Fin (n - 1)) (c : Colors Q n) : Colors Q n :=
  Function.update (Function.update c (leftSlot i) (c (rightSlot i)))
    (rightSlot i) (c (rightSlot i) ◃⁻¹ c (leftSlot i))

private theorem inverse_crossing {n : ℕ} (i : Fin (n - 1)) (c : Colors Q n) :
    inverseCrossing Q i (crossing Q i c) = c := by
  have hp := D5.S0.Certificates.Quandles.BraidColoringTransport.crossingInv_crossing
    (c (leftSlot i), c (rightSlot i))
  funext k
  by_cases h₁ : k = leftSlot i
  · subst k
    simpa only [crossing, inverseCrossing, Function.update_self,
      Function.update_of_ne (slots_ne i), Function.update_of_ne (Ne.symm (slots_ne i)),
      D5.S0.Certificates.Quandles.BraidColoringTransport.crossing,
      D5.S0.Certificates.Quandles.BraidColoringTransport.crossingInv] using
      congrArg Prod.fst hp
  · by_cases h₂ : k = rightSlot i
    · subst k
      simpa only [crossing, inverseCrossing, Function.update_self,
      Function.update_of_ne (slots_ne i), Function.update_of_ne (Ne.symm (slots_ne i)),
        D5.S0.Certificates.Quandles.BraidColoringTransport.crossing,
        D5.S0.Certificates.Quandles.BraidColoringTransport.crossingInv] using
        congrArg Prod.snd hp
    · simp [crossing, inverseCrossing, h₁, h₂]

private theorem crossing_inverse {n : ℕ} (i : Fin (n - 1)) (c : Colors Q n) :
    crossing Q i (inverseCrossing Q i c) = c := by
  have hp := D5.S0.Certificates.Quandles.BraidColoringTransport.crossing_crossingInv
    (c (leftSlot i), c (rightSlot i))
  funext k
  by_cases h₁ : k = leftSlot i
  · subst k
    simpa only [crossing, inverseCrossing, Function.update_self,
      Function.update_of_ne (slots_ne i), Function.update_of_ne (Ne.symm (slots_ne i)),
      D5.S0.Certificates.Quandles.BraidColoringTransport.crossing,
      D5.S0.Certificates.Quandles.BraidColoringTransport.crossingInv] using
      congrArg Prod.fst hp
  · by_cases h₂ : k = rightSlot i
    · subst k
      simpa only [crossing, inverseCrossing, Function.update_self,
      Function.update_of_ne (slots_ne i), Function.update_of_ne (Ne.symm (slots_ne i)),
        D5.S0.Certificates.Quandles.BraidColoringTransport.crossing,
        D5.S0.Certificates.Quandles.BraidColoringTransport.crossingInv] using
        congrArg Prod.snd hp
    · simp [crossing, inverseCrossing, h₁, h₂]

private def generator (n : ℕ) (i : Fin (n - 1)) : Equiv.Perm (Colors Q n) where
  toFun := crossing Q i
  invFun := inverseCrossing Q i
  left_inv := inverse_crossing Q i
  right_inv := crossing_inverse Q i

private theorem generator_distant (n : ℕ) (i j : Fin (n - 1))
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    generator Q n i * generator Q n j = generator Q n j * generator Q n i := by
  have h₁ : leftSlot i ≠ leftSlot j := by intro h; have := congrArg Fin.val h; simp only [leftSlot] at this; omega
  have h₂ : leftSlot i ≠ rightSlot j := by intro h; have := congrArg Fin.val h; simp only [leftSlot, rightSlot] at this; omega
  have h₃ : rightSlot i ≠ leftSlot j := by intro h; have := congrArg Fin.val h; simp only [leftSlot, rightSlot] at this; omega
  have h₄ : rightSlot i ≠ rightSlot j := by intro h; have := congrArg Fin.val h; simp only [rightSlot] at this; omega
  ext c k
  change crossing Q i (crossing Q j c) k = crossing Q j (crossing Q i c) k
  by_cases hk₁ : k = leftSlot i
  · subst k; simp [crossing, h₁, h₂, h₃, h₄, slots_ne, Ne.symm (slots_ne i)]
  · by_cases hk₂ : k = rightSlot i
    · subst k; simp [crossing, h₁, h₂, h₃, h₄, slots_ne, Ne.symm (slots_ne i)]
    · by_cases hk₃ : k = leftSlot j
      · subst k; simp [crossing, h₁, h₂, h₃, h₄, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₄, slots_ne]
      · by_cases hk₄ : k = rightSlot j
        · subst k; simp [crossing, h₁, h₂, h₃, h₄, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₄, slots_ne]
        · simp [crossing, hk₁, hk₂, hk₃, hk₄]

private theorem generator_adjacent (n : ℕ) (i j : Fin (n - 1))
    (hij : i.val + 1 = j.val) :
    generator Q n i * generator Q n j * generator Q n i =
      generator Q n j * generator Q n i * generator Q n j := by
  have h₁ : rightSlot i = leftSlot j := by apply Fin.ext; exact hij
  have h₂ : leftSlot i ≠ leftSlot j := by intro h; have := congrArg Fin.val h; simp only [leftSlot] at this; omega
  have h₃ : leftSlot i ≠ rightSlot j := by intro h; have := congrArg Fin.val h; simp only [leftSlot, rightSlot] at this; omega
  ext c k
  change crossing Q i (crossing Q j (crossing Q i c)) k =
    crossing Q j (crossing Q i (crossing Q j c)) k
  by_cases hk₁ : k = leftSlot i
  · subst k
    have hp := congrArg Prod.fst
      (D5.S0.Certificates.Quandles.BraidColoringTransport.crossing_yang_baxter
        (c (leftSlot i)) (c (leftSlot j)) (c (rightSlot j)))
    simpa [crossing, h₁, h₂, h₃, Ne.symm h₃, slots_ne,
      Ne.symm (slots_ne j),
      D5.S0.Certificates.Quandles.BraidColoringTransport.crossing₁,
      D5.S0.Certificates.Quandles.BraidColoringTransport.crossing₂] using hp
  · by_cases hk₂ : k = leftSlot j
    · subst k
      simp [crossing, h₁, h₂, h₃, Ne.symm h₂, Ne.symm h₃,
        slots_ne, Ne.symm (slots_ne i), Ne.symm (slots_ne j)]
    · by_cases hk₃ : k = rightSlot j
      · subst k
        simp [crossing, h₁, h₂, h₃, Ne.symm h₂, Ne.symm h₃,
          slots_ne, Ne.symm (slots_ne i), Ne.symm (slots_ne j)]
      · have hk₄ : k ≠ rightSlot i := by simpa [h₁] using hk₂
        simp [crossing, hk₁, hk₂, hk₃, hk₄]

private theorem generator_relators (n : ℕ) :
    ∀ r ∈ artinRelators n, FreeGroup.lift (generator Q n) r = 1 := by
  intro r hr
  rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
  · simp only [distantWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [generator_distant Q n i j hij]
    exact mul_inv_cancel _
  · simp only [adjacentWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [generator_adjacent Q n i j hij]
    exact mul_inv_cancel _

/-- The rack coloring action of the literal n-strand Artin group. -/
def braidAction (n : ℕ) : Artin n →* Equiv.Perm (Colors Q n) :=
  PresentedGroup.toGroup (generator_relators Q n)

private def extendPerm (n : ℕ) : Equiv.Perm (Colors Q n) →* Equiv.Perm (Colors Q (n + 1)) where
  toFun f := (Fin.snocEquiv (fun _ : Fin (n + 1) => Q)).permCongr
    (Equiv.prodCongr (Equiv.refl Q) f)
  map_one' := by ext c k; simp [Equiv.permCongr_apply, Fin.snocEquiv]
  map_mul' f g := by ext c k; simp [Equiv.permCongr_apply, Fin.snocEquiv]

private theorem extendPerm_snoc (n : ℕ) (f : Equiv.Perm (Colors Q n)) (c : Colors Q n) (z : Q) :
    extendPerm Q n f (Fin.snoc c z) = Fin.snoc (f c) z := by
  simp [extendPerm, Equiv.permCongr_apply, Fin.snocEquiv]

private theorem generator_include_snoc (n : ℕ) (i : Fin (n - 1)) (c : Colors Q n) (z : Q) :
    generator Q (n + 1) (includeGenerator n i) (Fin.snoc c z) =
      Fin.snoc (generator Q n i c) z := by
  have h₁ : leftSlot (includeGenerator n i) = (leftSlot i).castSucc := rfl
  have h₂ : rightSlot (includeGenerator n i) = (rightSlot i).castSucc := rfl
  change crossing Q (includeGenerator n i) (Fin.snoc c z) = Fin.snoc (crossing Q i c) z
  simp only [crossing, h₁, h₂, Fin.snoc_castSucc, ← Fin.snoc_update]

private theorem action_include (n : ℕ) :
    (braidAction Q (n + 1)).comp (strandInclusion n) =
      (extendPerm Q n).comp (braidAction Q n) := by
  apply PresentedGroup.ext
  intro i
  have hi : strandInclusion n (PresentedGroup.of i) =
      PresentedGroup.of (includeGenerator n i) := by
    change PresentedGroup.mk (artinRelators (n + 1))
      (FreeGroup.map (includeGenerator n) (FreeGroup.of i)) = _
    simp only [FreeGroup.map.of]
    rfl
  simp only [MonoidHom.comp_apply, hi, braidAction, PresentedGroup.toGroup.of]
  apply Equiv.ext
  intro c
  rw [← Fin.snoc_init_self c]
  rw [generator_include_snoc, extendPerm_snoc]

/-- Adding an untouched strand leaves the old transport and final color independent. -/
private theorem braidAction_include_snoc (n : ℕ) (b : Artin n) (c : Colors Q n) (z : Q) :
    braidAction Q (n + 1) (strandInclusion n b) (Fin.snoc c z) =
      Fin.snoc (braidAction Q n b c) z := by
  have h := DFunLike.congr_fun (action_include Q n) b
  simpa only [MonoidHom.comp_apply, extendPerm_snoc] using
    congrArg (fun f : Equiv.Perm (Colors Q (n + 1)) => f (Fin.snoc c z)) h

/-- The final old strand; positive strand count is required. -/
def lastSlot (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-- The positive last crossing in coordinates adapted to stabilization. -/
private theorem braidAction_last_snoc (n : ℕ) (hn : 0 < n) (c : Colors Q n) (z : Q) :
    braidAction Q (n + 1) (lastGenerator n hn) (Fin.snoc c z) =
      Fin.snoc (Function.update c (lastSlot n hn) (c (lastSlot n hn) ◃ z))
        (c (lastSlot n hn)) := by
  let i : Fin ((n + 1) - 1) := ⟨n - 1, by omega⟩
  have h₁ : leftSlot i = (lastSlot n hn).castSucc := rfl
  have h₂ : rightSlot i = Fin.last n := by apply Fin.ext; dsimp [rightSlot, i]; omega
  change generator Q (n + 1) i (Fin.snoc c z) = _
  change crossing Q i (Fin.snoc c z) = _
  simp only [crossing, h₁, h₂, Fin.snoc_castSucc, Fin.snoc_last,
    ← Fin.snoc_update, Fin.update_snoc_last]

/-- The negative last crossing in coordinates adapted to stabilization. -/
private theorem braidAction_last_inv_snoc (n : ℕ) (hn : 0 < n) (c : Colors Q n) (z : Q) :
    braidAction Q (n + 1) ((lastGenerator n hn)⁻¹) (Fin.snoc c z) =
      Fin.snoc (Function.update c (lastSlot n hn) z)
        (z ◃⁻¹ c (lastSlot n hn)) := by
  let i : Fin ((n + 1) - 1) := ⟨n - 1, by omega⟩
  have h₁ : leftSlot i = (lastSlot n hn).castSucc := rfl
  have h₂ : rightSlot i = Fin.last n := by apply Fin.ext; dsimp [rightSlot, i]; omega
  rw [map_inv]
  change (generator Q (n + 1) i).symm (Fin.snoc c z) = _
  change inverseCrossing Q i (Fin.snoc c z) = _
  simp only [inverseCrossing, h₁, h₂, Fin.snoc_castSucc, Fin.snoc_last,
    ← Fin.snoc_update, Fin.update_snoc_last]

end D5.S3.Topology.QuandleMarkovColoring

/-!
# Quandle colorings of algebraic braid closures

The coloring space of a closed algebraic braid is the fixed-point type of its
rack action. Quandle idempotence identifies both signed stabilization coloring
spaces with the original space: the added color is uniquely the old last color.
This is an algebraic Markov invariant; no geometric closure theorem is assumed.
-/

open scoped Quandles

namespace D5.S3.Topology.QuandleMarkovColoring

open D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation

variable {Q : Type*} [Quandle Q]

/-- Boundary colorings that agree after transport around the closed braid. -/
abbrev ClosedColorings (Q : Type*) [Rack Q] {n : ℕ} (b : Artin n) :=
  {c : Colors Q n // braidAction Q n b c = c}

private theorem positive_fixed_iff (n : ℕ) (hn : 0 < n)
    (b : Artin n) (c : Colors Q n) (z : Q) :
    braidAction Q (n + 1) (strandInclusion n b * lastGenerator n hn)
        (Fin.snoc c z) = Fin.snoc c z ↔
      braidAction Q n b c = c ∧ z = c (lastSlot n hn) := by
  rw [map_mul, Equiv.Perm.mul_apply, braidAction_last_snoc,
    braidAction_include_snoc, Fin.snoc_inj]
  constructor
  · rintro ⟨hc, hz⟩
    have hu : Function.update c (lastSlot n hn) (c (lastSlot n hn) ◃ z) = c := by
      rw [← hz]
      simp
    exact ⟨by simpa only [hu] using hc, hz.symm⟩
  · rintro ⟨hc, rfl⟩
    simpa using And.intro hc (rfl : c (lastSlot n hn) = c (lastSlot n hn))

private theorem negative_fixed_iff (n : ℕ) (hn : 0 < n)
    (b : Artin n) (c : Colors Q n) (z : Q) :
    braidAction Q (n + 1) (strandInclusion n b * (lastGenerator n hn)⁻¹)
        (Fin.snoc c z) = Fin.snoc c z ↔
      braidAction Q n b c = c ∧ z = c (lastSlot n hn) := by
  rw [map_mul, Equiv.Perm.mul_apply, braidAction_last_inv_snoc,
    braidAction_include_snoc, Fin.snoc_inj]
  constructor
  · rintro ⟨hc, hz⟩
    have hz' : c (lastSlot n hn) = z :=
      (Rack.left_cancel_inv z).mp (by simpa using hz)
    have hu : Function.update c (lastSlot n hn) z = c := by rw [← hz']; simp
    exact ⟨by simpa only [hu] using hc, hz'.symm⟩
  · rintro ⟨hc, rfl⟩
    simpa using And.intro hc (Quandle.fix_inv (x := c (lastSlot n hn)))

/-- Positive stabilization uniquely appends a copy of the last old color. -/
def positiveStabilizationEquiv (n : ℕ) (hn : 0 < n) (b : Artin n) :
    ClosedColorings Q b ≃
      ClosedColorings Q (strandInclusion n b * lastGenerator n hn) where
  toFun c := ⟨Fin.snoc c.val (c.val (lastSlot n hn)),
    (positive_fixed_iff n hn b c.val _).mpr ⟨c.property, rfl⟩⟩
  invFun d := ⟨Fin.init d.val, by
    have h := (positive_fixed_iff n hn b (Fin.init d.val) (d.val (Fin.last n))).mp
      (by simpa only [Fin.snoc_init_self] using d.property)
    exact h.1⟩
  left_inv c := by
    apply Subtype.ext
    simp only [Fin.init_snoc]
  right_inv d := by
    apply Subtype.ext
    have h := (positive_fixed_iff n hn b (Fin.init d.val) (d.val (Fin.last n))).mp
      (by simpa only [Fin.snoc_init_self] using d.property)
    change Fin.snoc (Fin.init d.val) ((Fin.init d.val) (lastSlot n hn)) = d.val
    rw [← h.2, Fin.snoc_init_self]

/-- Negative stabilization has the same diagonal extension and restriction maps. -/
def negativeStabilizationEquiv (n : ℕ) (hn : 0 < n) (b : Artin n) :
    ClosedColorings Q b ≃
      ClosedColorings Q (strandInclusion n b * (lastGenerator n hn)⁻¹) where
  toFun c := ⟨Fin.snoc c.val (c.val (lastSlot n hn)),
    (negative_fixed_iff n hn b c.val _).mpr ⟨c.property, rfl⟩⟩
  invFun d := ⟨Fin.init d.val, by
    have h := (negative_fixed_iff n hn b (Fin.init d.val) (d.val (Fin.last n))).mp
      (by simpa only [Fin.snoc_init_self] using d.property)
    exact h.1⟩
  left_inv c := by
    apply Subtype.ext
    simp only [Fin.init_snoc]
  right_inv d := by
    apply Subtype.ext
    have h := (negative_fixed_iff n hn b (Fin.init d.val) (d.val (Fin.last n))).mp
      (by simpa only [Fin.snoc_init_self] using d.property)
    change Fin.snoc (Fin.init d.val) ((Fin.init d.val) (lastSlot n hn)) = d.val
    rw [← h.2, Fin.snoc_init_self]

/-- Transport by the conjugating braid gives the closure-coloring equivalence. -/
def conjugationEquiv (n : ℕ) (b c : Artin n) :
    ClosedColorings Q b ≃ ClosedColorings Q (c * b * c⁻¹) where
  toFun d := ⟨braidAction Q n c d.val, by
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply, d.property]⟩
  invFun d := ⟨(braidAction Q n c)⁻¹ d.val, by
    have h := congrArg (fun x => (braidAction Q n c)⁻¹ x) d.property
    simpa only [map_mul, map_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h⟩
  left_inv d := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv d := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

/-- Number of fixed boundary colorings of a positive-strand algebraic braid. -/
noncomputable def coloringCount (Q : Type*) [Rack Q] [Finite Q] (b : PositiveBraid) : ℕ :=
  Nat.card (ClosedColorings Q b.2)

/-- Finite quandle coloring counts descend through all algebraic Markov moves. -/
theorem quandle_coloring_markov_invariant [Finite Q]
    {b c : PositiveBraid} (h : MarkovEquivalent b c) :
    coloringCount Q b = coloringCount Q c := by
  induction h with
  | rel b c h =>
    cases h with
    | conjugation n hn b c => exact Nat.card_congr (conjugationEquiv n b c)
    | positive n hn b => exact Nat.card_congr (positiveStabilizationEquiv n hn b)
    | negative n hn b => exact Nat.card_congr (negativeStabilizationEquiv n hn b)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end D5.S3.Topology.QuandleMarkovColoring

#print axioms D5.S3.Topology.QuandleMarkovColoring.positiveStabilizationEquiv
#print axioms D5.S3.Topology.QuandleMarkovColoring.negativeStabilizationEquiv
#print axioms D5.S3.Topology.QuandleMarkovColoring.quandle_coloring_markov_invariant
