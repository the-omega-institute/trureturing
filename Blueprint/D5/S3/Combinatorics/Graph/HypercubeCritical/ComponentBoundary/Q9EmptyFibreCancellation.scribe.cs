using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EmptyFibreCancellationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EmptyFibreCancellation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cancellation at an empty Q9 fibre",
        H("Cancellation at an empty first-axis fibre"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-empty-fibre-paired-residual-bound"),
            DeclarationHandle.Create(Module + ".paired_residual_bound"),
            H("The paired Huang sum requires singletons in both layers"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take a balanced cubic induced support with both lifts of a transverse row "
                    + "outside the support. The full Huang eigen-equation vanishes at both lifts. "
                    + "The first-axis entries vanish there, leaving the negative and positive "
                    + "transverse Huang blocks on the false and true layers, respectively.")),
                Paragraph(Text(
                    "The positive first-axis edges give equal switching signs on the two "
                    + "lifts of each paired neighbour. If k neighbours are paired and d is "
                    + "their signed transverse sum, each layer's singleton sum must be -d. "
                    + "Each singleton contributes a unit sign, and the paired and two singleton "
                    + "direction sets share the eight available directions. Hence k + 2|d| "
                    + "is at most eight.")),
                Paragraph(Text(
                    "The signed sum is an integer of parity k and magnitude at most k. "
                    + "Combining these facts gives |d| at most two. In particular three paired "
                    + "contacts at an empty row cannot all have the same sign. This is a local "
                    + "constraint for Hong, Wu and Xia's Problem 2. "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation")),
        ]));
}
