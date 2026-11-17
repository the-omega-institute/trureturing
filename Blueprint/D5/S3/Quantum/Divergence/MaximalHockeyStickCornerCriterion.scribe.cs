using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickCornerCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickCornerCriterion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact threshold obstruction for a singular diagonal contraction",
        H("The exact threshold obstruction for a singular diagonal contraction"), Blocks(
            Paragraph(Text("Only the weight restricted to the common interior must be positive definite. Endpoint weights, off-corner entries and empty corners remain in scope. This geometry is used in the singular functional-calculus criterion.")),
            Node("diagonal_optimal_iff", "For d_i in [0,1], t>0 and W whose subtype compression to 0<d_i<1 is positive definite, let D=diag(d), Y=diag(min(d,t(1-d))) and P the interior indicator. Y is weighted-optimal over positiveOverlaps D (t(1-D)) exactly when diag((d-t(1-d))_+) (PWP) diag((t(1-d)-d)_+)=0. Corner reduction and the faithful weighted criterion prove this equivalence; SingularCriterion consumes it.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-corner-criterion-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
