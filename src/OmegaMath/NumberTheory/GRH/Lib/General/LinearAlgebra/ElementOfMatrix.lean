import OmegaMath.NumberTheory.GRH.Lib.Adelic.Unitary.SpaceGram
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: The element of an adelic unitary group with a given isometric matrix. -/


variable {E} [Field E] [NumberField E] [NumberField.IsCMField E] {n} [Fintype n] {s : n → _}

/-- The element of the adelic unitary group of signs s given by an adelic matrix m with m*εm =
ε, ε the standard form. -/
noncomputable def G.ofMat m h := (toUnitary.symm (U.of isUnit_stdForm m h) : G E s)

@[simp] lemma G.mat_ofMat m h : (ofMat m h : G E s).mat = m := rfl
