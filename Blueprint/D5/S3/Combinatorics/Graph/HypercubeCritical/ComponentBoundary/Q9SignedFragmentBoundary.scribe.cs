using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SignedFragmentBoundaryDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedFragmentBoundary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed fragments of balanced cubic supports in the nine-cube",
        H("Signed boundary and completion bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-signed-fragment-forces-exterior-contacts"),
                DeclarationHandle.Create(Module + ".card_add_abs_le"),
                H("The known signs force additional contacts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a fragment of an induced Huang-balanced cubic support with its switching signs. "
                        + "At an exterior vertex, the full Huang row vanishes. Each new contact can cancel "
                        + "at most one unit of the fragment's signed sum. The full contact count is therefore "
                        + "at least the known count plus the absolute value of that sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-signed-fragment-shared-contact-capacity"),
                DeclarationHandle.Create(Module + ".shared_contacts_le_of_fragment"),
                H("A separated support has fewer available contacts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When a vertex sees the fragment and another disjoint nonadjacent balanced cubic support, "
                        + "the two full supports can use at most six contact directions there. The fragment's "
                        + "known contacts and the contacts needed to cancel its signed sum consume part of "
                        + "that budget before the first support is completed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-signed-fragment-completion-order"),
                DeclarationHandle.Create(Module + ".fragment_size_bound"),
                H("The signed boundary bounds the order of any completion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Summing the contact bound over the exterior charges every further vertex through "
                        + "its incident edges. Inside the completion, sign coherence makes the absolute "
                        + "signed sum equal to the fragment's contact count. Double counting gives three "
                        + "times the fragment order plus the sum of the absolute signed rows at most six "
                        + "times the completion order."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "These inequalities constrain candidate supports for Problem 2 of Hong, Wu and Xia, "
                + "which asks for a 258-vertex subcubic support in the nine-cube. "
                + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))
        ]));
}
