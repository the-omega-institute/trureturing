using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class TotalUnimodularL1RepairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair.";

    private static readonly LibraryNoteRef InnerInverseSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/fampalee2018sparse");

    private static readonly LibraryNoteRef SplittingSource =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/sontag1980generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite totally unimodular integer systems admit integral repairs at the cost of any feasible real solution.",
        H("Integral L1 Repair for Totally Unimodular Matrices"),
        Blocks(
            DescribeDeclaration("nonzeroSupport", "Nonzero coordinates", DescribeRole.Definition,
                "Take the finite set of indices where a vector is nonzero."),
            DescribeDeclaration("mem_nonzeroSupport", "Membership in the support", DescribeRole.Theorem,
                "A coordinate belongs to this set exactly when its value is nonzero."),
            DescribeDeclaration("fromCols_neg_isTotallyUnimodular", "Signed column doubling", DescribeRole.Theorem,
                "An integer matrix and its negation can be placed side by side while preserving total unimodularity. Each minor of the doubled matrix differs from the corresponding indexed minor by a product of column signs."),
            DescribeDeclaration("exists_integer_l1_repair", "An integral solution within the real L1 cost", DescribeRole.Theorem,
                "The matrix has finite row and column types and every square minor has determinant zero, one, or minus one. The right-hand side is integral and the given real vector solves the real scalar extension of that same system. The conclusion gives an integer solution whose sum of absolute coordinates is at most the real vector's cost.",
                "Split the real vector into positive and negative parts. A feasible step in a supported kernel direction removes a nonzero coordinate without raising the cost. Once the supporting columns are independent, the integral inner inverse reconstructs the restricted solution. Subtract the two nonnegative integer parts to recover the signed repair."),
            DescribeDeclaration("support_card_le_sum_abs", "Integer support is bounded by L1 cost", DescribeRole.Theorem,
                "Each nonzero integer coordinate contributes at least one to the sum of absolute values."),
            DescribeDeclaration("reduce_integer_solution", "Reduction of an integer solution", DescribeRole.Theorem,
                "For each natural number n, reduction in ZMod n carries the integer matrix equation to the reduced system. The support of the reduced vector is contained in the integer support."),
            DescribeDeclaration("exists_zmod_repair_with_support_bound", "Modular repair from a real solution", DescribeRole.Theorem,
                "For a totally unimodular integer matrix and a feasible real solution with integral right-hand side, the cardinality of the repair's support over ZMod n is bounded by the real L1 cost."),
            Paragraph(Text(
                "The integral-feasibility principle is classical. Hoffman and Kruskal's Integral Boundary Points of Convex Polyhedra (1956) gives the polyhedral integrality background. The Lean construction uses the repository's IntegerMatrixInnerInverse theorem and its selected-minor and splitting antecedents in Fampa and Lee and in Sontag.")))));

    private static DocumentBlock.Describe DescribeDeclaration(string name, string title, DescribeRole role, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(InnerInverseSource, SplittingSource),
            Blocks(paragraphs.Select(paragraph => Paragraph(Text(paragraph))).ToArray()), role);
}
