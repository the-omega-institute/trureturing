using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaRootEvaluationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaRootEvaluation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Laurent support justifies the complete cubic-root evaluation of the Jacobi cube.", H("CubicThetaRootEvaluation"), Blocks(
            Paragraph(Text("Finite Laurent support justifies the complete cubic-root evaluation of the Jacobi cube.")),
            Node("0", "indexEquiv", "The quotient and nonnegative remainder give a genuine equivalence Fin 3 times Z with Z.", DescribeRole.Definition),
            Node("1", "map_T_residue", "A ring evaluation with T(3)=1 depends only on the integer Laurent residue.", DescribeRole.Theorem),
            Node("2", "hasSum_evaluated_columns", "Evaluation of every Laurent column reconstructs the actual Jacobi cube.", DescribeRole.Theorem),
            Node("3", "hasSum_map", "A coefficient ring map from discrete rationals preserves the full formal-power-series sum.", DescribeRole.Theorem),
            Node("4", "evaluated_jacobi_cube", "The full evaluated cube uses all three residue sums, with their exact phases and signs.", DescribeRole.Theorem),
            Paragraph(Text("These are attributed classical intermediate identities. CubicThetaIdentities proves the downstream Borwein relations and EtaSignK6 proves the exact all-index sign theorem. Independent formal acceptance and publication remain separate. No priority or unique claim is made."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-root-evaluation-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
