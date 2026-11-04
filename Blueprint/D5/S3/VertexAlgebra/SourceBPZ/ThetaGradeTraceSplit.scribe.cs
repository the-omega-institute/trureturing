using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class ThetaGradeTraceSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SourceBPZ/ThetaGradeTraceSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The theta trace on each finite energy grade is the fixed-minus-anti-fixed dimension.",
        H("Theta Grade Trace Split"),
        Blocks(
            Paragraph(Text(
                "For a positive-definite lattice datum D and an integer energy grade n, grade D n is finite-dimensional. Its theta-even part is grade D n intersect fixedSpace D, and its theta-odd part is grade D n intersect minusSpace D.")),
            Law("grade_theta_trace_eq_fixed_minus_anti", "Twined trace splits by theta eigenspaces",
                "For every positive-definite D and integer n, the trace of theta on grade D n equals the complex dimension of its theta-fixed submodule minus the complex dimension of its theta-anti-fixed submodule.")),
        []));

    private static DocumentBlock Law(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("theta-grade-trace-split-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
