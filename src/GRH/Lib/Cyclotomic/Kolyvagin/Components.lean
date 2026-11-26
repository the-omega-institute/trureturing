import GRH.Lib.ClassField.Places.Conjugation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Stickelberger annihilation and Kolyvagin–Rubin bound for odd twisted components (known
result; see Lib.Cyclotomic.Kolyvagin.ComponentBound).

Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand quotient
(known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Locally constant cocycles for a character with vanishing conditions; the odd
component. -/

variable {O} [CommRing O] {N} (l e : ℕ) [NeZero N] [Fact l.Prime] [Algebra ℤ_[l] O]
  (ψ : DirichletCharacter O N)

/-- The character Υ = cyc^e·ψ of Gal(ℚ̄/ℚ) with values in O^×: cyc is the l-adic cyclotomic
character, and ψ is read through the action on N-th roots of unity. -/
noncomputable def cycPowDirichlet :=
  cycCharIn (Γ := Gal(Ω/ℚ)) O Ω l ^ e * ψ.toUnitHom.comp (cycCharMod Ω N)

/-- The O-module of locally constant maps x : Gal(Ω/ℚ) → B with x(gh) = x(g) + χ(g)x(h) (cocycles
for the character χ) that vanish on the set s. -/
noncomputable def vanishingCocycles (χ : Gal(Ω/ℚ) →* Oˣ) B [AddCommGroup B] [Module O B] (s :
  Set _) := locConst (O := O) B ⊓ ⟨⟨⟨{x | (∀ g h, x (g * h) = x g + (χ g).1 • x h) ∧ ∀ g ∈ s,
  x g = 0}, by simp_all; grind⟩, by simp⟩, by simp_all [smul_comm (χ _).1]⟩

/-- The elements of Gal(Ω/ℚ(μ_N)) lying in the inertia group of some place above neither l nor
any prime of T. -/
def inertiaOff (N l : ℕ) [NeZero N] (T : Finset Nat.Primes) := {i | ∃ A, (i ∈ cycloGalGroup N ∧
  A.valuation l = 1 ∧ i ∈ inertiaGroup _ A) ∧ ∀ r ∈ T, ¬A.valuation (r : Ω) < 1}

/-- The locally constant O/l^ν-valued cocycles for (cyc^eψ)⁻¹ vanishing at `cmConj`, on inertia over
ℚ(μ_N) away from l, and on decomposition groups over ℚ(μ_{Nl^∞}) above l. -/
noncomputable abbrev component ν := vanishingCocycles (cycPowDirichlet l e ψ)⁻¹ (QuotSpan (l ^ ν :
  O)) (insert cmConj (cycloGalGroup N ∩ (inertiaAbove (placesDividing ℚ l)ᶜ ∪ shaLocalSet l ℚ 1)))
