import GRH.Lib.Weil.MixedModel.NameWeilAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

Part of: Galois action on CM theta functions and on the finite Weil representation (known result;
see Lib.CM.Reciprocity.SemilinearWeilLaw).

This file: Definition of tight frames in the unimodular lattice, with multiplicities. Definition:
orthogonality relation between translates of the vacuum and of a finite vector. Relation: jets of
one vector are Galois conjugates of those of another. -/

variable {E I : Type} [Field E] [CMType E] [WeilData E] (w : I → E) [Fintype I]

/-- The finite image of γ in E^n: the finite adelic vector α⁻¹γ, with α the idele of the Weil
data. -/
noncomputable def finiteImage := (‹WeilData E›.α⁻¹.1 • Algebra.linearMap E (𝔸f E)).compLeft I

/-- The w_i lie in the lattice E ∩ αÔ and, taken m_i times, form a tight frame of length M: ∑
m_i σ(w_i)·conj(τ(w_i)) = Mδ_{στ} for σ, τ in the CM type. -/
def IsTightFrame (m : I → ℕ) (M : ℕ) := (∀ i, finiteImage w i ∈ Ô E) ∧ ∀ σ τ, ∑ i, m i *
    (Φ σ (w i) * starRingEnd ℂ (Φ τ (w i))) = ite (σ = τ) ↑M 0

lemma IsTightFrame.repeat_vectors {m M} (h : IsTightFrame w m M) : IsTightFrame (fun x : Σ i,
  Fin (m i) ↦ w x.1) 1 M := by simp_all [IsTightFrame, finiteImage, Fintype.sum_sigma]

/-- Orthogonality data for F: N^{2fn} > 0 finite vectors x_j with δx_j integral (f infinite
places, rank n), and m ∈ ℕ with ∑_j m·ℓ(ϱ(αx_j)vac)·ϱ(−αx_j)F = N^{2fn}·ℓ(F)·vac for all
linear forms ℓ. -/
structure Space.VacuumExpansion {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] {s} (V :
  Space E n s) (δ : E) (N F) where
  (Index) [fintypeIndex : Fintype Index] [nonempty : Nonempty Index] (shift : Index → n →
    𝔸f E) (multiplier : ℕ) mul_shift_mem j i : δ * shift j i ∈ Ô E
  card_dvd : Fintype.card Index = N ^ (2 * Fintype.card (NumberField.InfinitePlace E × n))
  sum_eq (ℓ : _ →ₗ[ℂ] ℂ) : ∑ j, (multiplier * ℓ (V.ϱ (finVec (shift j)) V.vacElem)) • V.ϱ (finVec
    (-shift j)) F = (Fintype.card Index * ℓ F) • V.vacElem

/-- The series T_t f with σ applied to its coefficients equals T_{t'} f' with the places of its
variables renamed by π⁻¹. -/
abbrev Space.IsJetConjugate [Field I] [CMType I] [WeilData I] {n : Type} [Fintype n] {s} {V :
  Space I n s} σ (π : Equiv.Perm _) t t' f f' := (V.jetSeries t f).map σ =
  (V.jetSeries t' f').rename (.map π.symm id)

@[simp] lemma Space.constantCoeff_jetSeries {s} {V : Space E I s} t f :
    (V.jetSeries t f).constantCoeff = V.θ (V.projReal f) := (jetSeries_apply ..).trans (by simp)
