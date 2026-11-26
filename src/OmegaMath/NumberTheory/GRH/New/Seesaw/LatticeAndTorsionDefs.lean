import OmegaMath.NumberTheory.GRH.Lib.CM.Sigma.PadicSeriesDefs
import OmegaMath.NumberTheory.GRH.Lib.Weil.Periods.DegreeAndUnipotent
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Lattice basis `gradedLatticeBasis`, admissible combinations of translates with controlled
denominators and size. -/

open Matrix

/-- A basis matrix with string rows multiplied by u: for odd s the identity with column e
replaced by e/π̄ + z/(ππ̄) (e last in X, z middle); for even s diag(1; a⁻¹, …, a⁻¹, ā, …,
ā). -/
noncomputable def gradedLatticeBasis {R X' ι : Type*} {s} [CommRing R] [StarRing R] (e :
  (X' ⊕ Unit) ⊕ Fin s ≃ ι) (a π : Rˣ) (u : unitary R) := reindex e e (fromBlocks (ite (Odd s)
  (diagonal (1 ⊕ᵥ fun _ ↦ (star π)⁻¹.1)) 1) 0 (of fun b ↦ 0 ⊕ᵥ fun _ ↦ ite (b = b.rev)
  (u * (star π * π)⁻¹.1) 0) (diagonal fun b ↦ u * ite (Odd s) 1 (ite (2 * b < s) a⁻¹.1 (star a))))

variable {E X' ι : Type*} [Field E] [CMType E] (q : ℕ)

/-- The condition that the finite frame x_f of V spans the same Ô-lattice as `gradedLatticeBasis`:
x_f = gradedLatticeBasis·k for some k in GL(Ô). -/
def Grading.SpansLattice [Fintype ι] {ε s N} {V : Space E ι ε} (Y : Grading V N (X' ⊕ _) s) a π u :=
  ∃ k ∈ intGL ι (Ô E), V.xFin.1 = gradedLatticeBasis Y.indexEquiv a π u * k.1

/-- The subring of complex numbers whose image under every ring homomorphism ℂ → ℂ_l is
integral, for every prime l coprime to n. -/
def integralAway n := (by use! {z | ∀ l [Fact l.Prime], l.Coprime n → ∀ ι : _ →+* ℂ_[l], ‖ι z‖ ≤
        1} <;> simp <;> grind [mul_le_one₀, IsUltrametricDist.norm_add_le_max] : Subring ℂ)

/-- The conditions on a finitely supported r: support in A, each d·r(x) integral away from n
and, if p holds, ∑|σ r(x)| ≤ B for all automorphisms σ of ℂ. -/
structure IsAdmissibleCoeffs {X} (A : Set X) (n d : ℕ) (p : Prop) B (r : X →₀ ℂ) where
  support_subset : ∀ x ∈ r.support, x ∈ A
  integral x : d * r x ∈ integralAway n
  size_le : p → ∀ σ : ℂ ≃+* ℂ, r.sum (fun _ ↦ (‖σ ·‖)) ≤ B

section

variable {E ι : Type*} [Field E] [NumberField E] (q : ℕ)

/-- The group of finite adelic vectors x such that d_i x_i is integral at every place not
dividing q, for each index i. -/
def weightedTranslations (d : ι → 𝔸f E) : AddSubgroup (ι → 𝔸f E) :=
  ⟨⟨⟨{x | ∀ i (w : FinPlace E), ↑q ∉ w.1 → Valued.v
  ((d i * x i) w) ≤ 1}, by simp_all [-map_mul, mul_add, Valued.v.map_add_le]⟩, by simp⟩, by simp⟩

/-- The group of finite adelic vectors x indexed by ι such that d·x is integral at every place
not dividing q. -/
abbrev translations ι q d := weightedTranslations (E := E) q fun _ : ι ↦ d

end

/-- N = π·π̄ for the finite idele π, which is a uniformiser at the places of P and a unit
elsewhere, and P is disjoint from its conjugate. -/
def IsSplitSquarefree (P : Finset (FinPlace E)) (N : E) (π : (𝔸f E)ˣ) := ↑N = π * star π.1 ∧ ∀ w,
  Valued.v (π.1 w) = ite (w ∈ P) (.exp (-1)) 1 ∧ (w ∈ P → star w ∉ P)
