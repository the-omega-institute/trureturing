using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BinaryDecimationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/BinaryDecimation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "BinaryDecimation",
        H("BinaryDecimation"),
        Blocks(
            Paragraph(Text("These common algebraic mechanisms use fixed coefficients on every natural input. There is no independence, invertibility, domain, characteristic-zero or Noetherian hypothesis. Cayley-Hamilton and linear-recurrence uniqueness are reused from the pinned Mathlib.")),
            Node("MatrixFamily", "Fixed matrices over a commutative ring, all inputs, both digits, arbitrary positive dimension.", DescribeRole.Definition),
            Node("ClosedFamily", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("ArbitraryFamily", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("closed_matrix_iff", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("arbitrary_matrix_iff", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("dyadic_matrix_recurrence", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("shifted_sub_solution", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem))));

    private static string Exact(string name) => name switch
    {
        "MatrixFamily" => "Exact source statement: def MatrixFamily (a : ℕ → R) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ F : ℕ → Fin d → R, ∃ M0 M1 : Matrix (Fin d) (Fin d) R, (∀ n, F n ⟨0, hd⟩ = a n) ∧ (∀ n, F (2 * n) = M0.mulVec (F n)) ∧ (∀ n, F (2 * n + 1) = M1.mulVec (F n))",
        "ClosedFamily" => "Exact source statement: def ClosedFamily (a : ℕ → R) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ b : Fin d → ℕ → R, ∃ c0 c1 : Fin d → Fin d → R, (∀ n, b ⟨0, hd⟩ n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)",
        "ArbitraryFamily" => "Exact source statement: def ArbitraryFamily (a : ℕ → R) : Prop := ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι; ∃ (b : ι → ℕ → R) (i0 : ι) (c0 c1 : ι → ι → R), (∀ n, b i0 n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)",
        "closed_matrix_iff" => "Exact source statement: theorem closed_matrix_iff (a : ℕ → R) : ClosedFamily a ↔ MatrixFamily a",
        "arbitrary_matrix_iff" => "Exact source statement: theorem arbitrary_matrix_iff (a : ℕ → R) : ArbitraryFamily a ↔ MatrixFamily a",
        "dyadic_matrix_recurrence" => "Exact source statement: theorem dyadic_matrix_recurrence [Nontrivial R] (a : ℕ → R) (ha : MatrixFamily a) : ∃ E : LinearRecurrence R, 0 < E.order ∧ E.IsSolution (fun n => a (2 ^ (n + 2) + 1))",
        "shifted_sub_solution" => "Exact source statement: theorem shifted_sub_solution (E : LinearRecurrence R) (u : ℕ → R) (hu : E.IsSolution u) (t : R) : E.IsSolution (fun n => u (n + 1) - t * u n)",
        _ => name
    };

    private static DocumentBlock Node(string name, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("binarydecimation-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose)), Paragraph(Text(Exact(name)))), role);
}
