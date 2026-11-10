using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BinaryDecimationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/BinaryDecimation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "BinaryDecimation", H("BinaryDecimation"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("Fixed binary matrices and finite indexed families are over an arbitrary commutative unital ring R. Matrix recurrence theorems additionally assume 1 is not 0. The given matrix dimension d is exactly the monic forward recurrence order. All natural inputs are retained. There is no basis, independence, invertibility, characteristic-zero, domain or Noetherian assumption. Cayley-Hamilton and recurrence uniqueness come from pinned Mathlib. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("MatrixFamily", "Exact source declaration: def MatrixFamily (a : ℕ → R) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ F : ℕ → Fin d → R, ∃ M0 M1 : Matrix (Fin d) (Fin d) R, (∀ n, F n ⟨0, hd⟩ = a n) ∧ (∀ n, F (2 * n) = M0.mulVec (F n)) ∧ (∀ n, F (2 * n + 1) = M1.mulVec (F n))", DescribeRole.Definition),
            Node("ClosedFamily", "Exact source declaration: def ClosedFamily (a : ℕ → R) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ b : Fin d → ℕ → R, ∃ c0 c1 : Fin d → Fin d → R, (∀ n, b ⟨0, hd⟩ n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)", DescribeRole.Definition),
            Node("ArbitraryFamily", "Exact source declaration: def ArbitraryFamily (a : ℕ → R) : Prop := ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι; ∃ (b : ι → ℕ → R) (i0 : ι) (c0 c1 : ι → ι → R), (∀ n, b i0 n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)", DescribeRole.Definition),
            Node("closed_matrix_iff", "Exact source declaration: theorem closed_matrix_iff (a : ℕ → R) : ClosedFamily a ↔ MatrixFamily a", DescribeRole.Theorem),
            Node("arbitrary_matrix_iff", "Exact source declaration: theorem arbitrary_matrix_iff (a : ℕ → R) : ArbitraryFamily a ↔ MatrixFamily a", DescribeRole.Theorem),
            Node("dyadic_fixed_matrix_recurrence", "Exact source declaration: theorem dyadic_fixed_matrix_recurrence [Nontrivial R] (a : ℕ → R) (d : ℕ) (hd : 0 < d) (F : ℕ → Fin d → R) (M0 M1 : Matrix (Fin d) (Fin d) R) (hf : ∀ n, F n ⟨0, hd⟩ = a n) (he : ∀ n, F (2 * n) = M0.mulVec (F n)) (ho : ∀ n, F (2 * n + 1) = M1.mulVec (F n)) : ∃ E : LinearRecurrence R, E.order = d ∧ E.IsSolution (fun n => a (2 ^ (n + 2) + 1))", DescribeRole.Theorem),
            Node("dyadic_matrix_recurrence", "Exact source declaration: theorem dyadic_matrix_recurrence [Nontrivial R] (a : ℕ → R) (ha : MatrixFamily a) : ∃ E : LinearRecurrence R, 0 < E.order ∧ E.IsSolution (fun n => a (2 ^ (n + 2) + 1))", DescribeRole.Theorem),
            Node("shifted_sub_solution", "Exact source declaration: theorem shifted_sub_solution (E : LinearRecurrence R) (u : ℕ → R) (hu : E.IsSolution u) (t : R) : E.IsSolution (fun n => u (n + 1) - t * u n)", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("binarydecimation-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
