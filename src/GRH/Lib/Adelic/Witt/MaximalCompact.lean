import GRH.Lib.Adelic.Witt.SpaceOperations
import GRH.Lib.General.LinearAlgebra.ExpSurjective
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

Part of: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa decomposition
(known result; see Lib.SiegelWeil.SingularForms.AdaptedHom).

This file: Block embedding of U(Y) into U(Y ⊕ Y'). Maximal compact subgroup of the adelic unitary
group and its compactness. -/

/-- The block embedding a ↦ diag(a, 1) of U(diag ε) into the unitary group of the concatenated
signs (ε, η). -/
@[simps! apply_coe_val] noncomputable def U.inl {n m} [Fintype n]
  [Fintype m] (ε : n → _) (η : m → _) := (sum (signMatrix_sum ε η)).comp (.inl ..)

variable (E) {n} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n] (s : n → ℤˣ)

/-- The subgroup K_∞K₀ of G: elements that are unitary matrices at each infinite place and lie
in GL_n(Ô) at the finite places. -/
noncomputable def maxCompact : Subgroup (G E s) := .prod (.pi .univ fun _ ↦ maxCompactU s) (Kf ..)

variable {E s}

lemma isCompact_maxCompact : IsCompact (maxCompact E s : Set (G E s)) := (isCompact_univ_pi fun _ ↦
  isCompact_iff_compactSpace.2 ⟨@isCompact_univ (maxCompactU s) _ _⟩).prod isCompact_Kf
