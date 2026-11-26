import OmegaMath.NumberTheory.GRH.Lib.ClassField.GaloisCohomology.ContinuousCocycles
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.GaloisDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Discrete Q/Z, continuous characters and the cyclic symbol δχ ∪ w. -/

noncomputable section

/-- The group ℚ/ℤ; it is given the discrete topology. -/
def QZ := AddCircle (1 : ℚ) deriving AddCommGroup, DivisibleBy _ ℤ

instance : TopologicalSpace QZ := ⊥

instance : DiscreteTopology QZ := ⟨rfl⟩

/-- The quotient homomorphism ℚ → ℚ/ℤ. -/
def QZ.mk : ℚ →+ QZ := QuotientAddGroup.mk' _

variable (a : QZ) {R} (G) {M} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M)

/-- For a class a in ℚ/ℤ, its unique rational representative in the interval [0,1). -/
def QZ.fracRep := (a.equivIco 1 0).1

/-- For a, b in ℚ/ℤ, the integer part of the sum of their representatives in [0,1), an integer
equal to 0 or 1. -/
def QZ.carry b := ⌊fracRep a + fracRep b⌋

@[simp] lemma QZ.mk_fracRep : mk a.fracRep = a := a.coe_equivIco

lemma QZ.fracRep_mk r : fracRep (mk r) = Int.fract r := toIcoMod_zero_one r

@[push_cast] lemma QZ.cast_carry b : carry a b = fracRep a + fracRep b - fracRep (a + b) := by
  simp [carry, ← Int.self_sub_fract, ← fracRep_mk]

/-- Continuous characters `G → ℚ/ℤ`. -/ abbrev QZChar := Z1 (.trivial ℤ G QZ)

variable {G}

/-- The class δχ ∪ w in H²(G,M) of the cocycle (g,h) ↦ carry(χ(g), χ(h))·w, biadditive in the
character χ: G → ℚ/ℤ and the invariant w. -/
def cyclicClass : QZChar G →+ ρ.invariants →+ H2 ρ := by refine (.mk' (fun χ ↦ .mk' (fun w ↦
  ⟦⟨fun p ↦ (χ.1 p.1).carry (χ.1 p.2) • w, χ.2.imp (by fun_prop) ?_⟩⟧) ?_) fun ⟨χ, _, _⟩ ⟨ψ, _, _⟩ ↦
  AddMonoidHom.ext fun w ↦ QuotientAddGroup.eq_iff_sub_mem.2 ⟨fun g ↦
  (χ g).carry (ψ g) • -w, by fun_prop, ?_⟩) <;> intros <;>
  simp_all [(ρ.mem_invariants _).1 (Subtype.prop _)] <;>
  first | rfl | (match_scalars; qify; grind)
