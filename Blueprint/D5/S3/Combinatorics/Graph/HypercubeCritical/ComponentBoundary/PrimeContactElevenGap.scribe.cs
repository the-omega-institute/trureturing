using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class PrimeContactElevenGapDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "PrimeContactElevenGap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven-cycle coordinate rigidity and the eleven-column exclusion",
        H("Seven-cycle coordinate rigidity and the eleven-column exclusion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("seven-cycle-unique-chord"),
                DeclarationHandle.Create(Module + ".seven_cycle_chord_unique"),
                H("A seven-cycle with no triangle on a cycle edge has at most one chord"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Label each edge by the two changed axes. Consecutive labels are "
                    + "disjoint, and each used axis occurs exactly twice by closure "
                    + "of the seven-cycle. A distance-three chord requires equality "
                    + "of the first and third labels. Two such equal pairs contradict "
                    + "the allowed label pattern or give a triangle containing a cycle edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-contact-eleven-gap"),
                DeclarationHandle.Create(Module + ".card_ne_eleven_of_twoContact"),
                H("The two-contact cube cannot have eleven columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The weighted order counts and triangle incidence leave two "
                        + "possible graphs after triangle edges are removed. A four-cycle "
                        + "needs twelve distinct columns because its triangle attachments "
                        + "cannot overlap. A seven-cycle requires at least two chords, "
                        + "contradicting coordinate rigidity.")),
                    Paragraph(Text(
                        "Together with the preceding cardinality gap this gives "
                        + "nine or at least twelve columns in the two-contact branch "
                        + "of Hong, Wu and Xia's open problem. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactCardinalityGap"))]));
}
