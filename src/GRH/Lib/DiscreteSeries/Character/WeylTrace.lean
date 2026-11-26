import GRH.Lib.Shimura.TraceFormula.DefiniteTrace
import GRH.Lib.Adelic.CuspForms.WeightParameter
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Weyl character and dimension formulas for U(n) and products of unitary groups (known
result; see Lib.DiscreteSeries.Character.KTypeMultiplicity).

This file: Weyl character formula at regular semisimple elements of products of GL_n. -/

variable {a} {ι : Type} [Fintype ι]

lemma det_zpow_add {r : Fin a → ℂ} {g : GL (Fin a) ℂ} (h : ∀ i, g.1.charpoly.IsRoot (r i)) d
    (k : _ → ℤ) : (Matrix.of fun i j ↦ r i ^ (d + k j)).det = Finset.univ.prod r ^ d * (Matrix.of
  (r · ^ k ·)).det := by simpa [← Finset.prod_zpow, zpow_add₀ (spectrum.ne_zero_of_mem_of_unit
  (Matrix.mem_spectrum_of_isRoot_charpoly (h _)))] using! Matrix.det_mul_column ..

/-- Weyl's character formula: if each g_v in GL_a(ℂ) has distinct eigenvalues x_{v,i}, the trace
of `weylRep` κ e at g times ∏_v det(x_{v,i}^j) equals ∏_v det(x_{v,i}^(e_v + λ_{v,a−1−j} +
j)), with 0 ≤ i, j < a and λ the weight `diagramWeight` of κ.

Known result: Weyl character and dimension formulas for U(n) and products of unitary groups. -/
lemma trace_weylRep κ e {g : ι → GL (Fin a) ℂ} {x : ι → Fin a ↪ ℂ}
    (hg : ∀ v i, (g v).1.charpoly.IsRoot
    (x v i)) : (weylRep κ e g).trace * ∏ v, (Matrix.vandermonde (x v)).det = ∏ v, Matrix.det
    (.of fun i j : Fin a ↦ x v i ^ (e v + ↑(diagramWeight (rankAt (Fin a)) κ (v, j.rev) + j))) := by
  choose h hh using (isConj_diagonal_of_isRoot_charpoly <| hg ·)
  rw [← mul_inv_cancel_right g h, map_mul, Matrix.trace_mul_comm, ← map_mul]
  simpa [weylRep, ← (hh _).eq, mul_assoc, Units.smul_def, det_zpow_add (hg _)] using .inl
    (weyl_character 1 _)
