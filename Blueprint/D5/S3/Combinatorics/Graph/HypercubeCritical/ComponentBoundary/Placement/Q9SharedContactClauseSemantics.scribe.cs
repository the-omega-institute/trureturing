using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SharedContactClauseSemanticsDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9SharedContactClauseSemantics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubicity and exterior evenness constrain neighbor bits and their prefix parity.",
        H("Degrees and parity in the neighbor list"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-degree"),
                DeclarationHandle.Create(Owner + "upperDegree"),
                H("Among four axes some neighbor is omitted"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An occupied vertex has three occupied neighbors, so four distinct axes cannot all "
                    + "lead to occupied vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-degree"),
                DeclarationHandle.Create(Owner + "lowerDegree"),
                H("Among seven axes some neighbor is occupied"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At an occupied vertex, only six axes can lead to omitted vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-parity-last"),
                DeclarationHandle.Create(Owner + "prefixParity_last"),
                H("Final neighbor parity equals occupancy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The last prefix contains all nine directions. Its degree is odd at an occupied vertex "
                    + "and even at an exterior vertex. The prefix starts with the first neighbor bit and "
                    + "updates by exclusive-or with the next neighbor bit."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactNormalized"))
        ]));
}
