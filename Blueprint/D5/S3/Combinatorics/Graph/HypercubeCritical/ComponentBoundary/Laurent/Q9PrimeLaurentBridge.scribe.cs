using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9PrimeLaurentBridgeDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Laurent/Q9PrimeLaurentBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a connected induced cubic subgraph of the nine-cube with a nonempty chosen parity side, a nonzero defect kernel at distinct prime weights detects the Laurent identity when every row on that side has a partition of the axes by neighbor direction triples.",
        H("Prime weights and Laurent transport on the nine-cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-prime-defect-laurent-equivalence"),
                DeclarationHandle.Create(Owner + "prime_defect_kernel_iff_laurentIdentity"),
                H("One prime specialization detects the Laurent identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At each selected vertex, require its three opposite-parity neighbors' direction triples to partition the nine axes. Each exterior axis then occurs as the second axis of exactly one two-step path. Reversal of ordered paths expresses twice the defect quadratic form as a sum of squared edge residuals. A kernel makes every residual vanish. Distinct prime valuations turn the resulting weight ratios into integer exponent differences. Conversely, the Laurent potential gives a nonzero kernel whenever every real coordinate weight is nonzero, by monomial evaluation."))),
                DescribeRole.Theorem),
            Paragraph(Text("For Hong, Wu and Xia's Problem 2, the partition hypothesis remains an independent condition on the candidate component. See https://arxiv.org/html/2610.09483v1#Thmproblem2."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Laurent/Q9LaurentDirectionTypes")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactTransport")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9WeightedSaturation"))
        ]));
}
