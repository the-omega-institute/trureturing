using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SweepDimension;

internal sealed class SweepUpperDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/boldi2026sweep");
    private const string Prefix = "D5/S3/Combinatorics/SweepDimension/Upper.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite poset has sweep dimension equal to its maximum three-chain-free cardinality.", H("The exact sweep dimension"),
        Blocks(
            Describe.Lean(DescribeId.Create("theta-bound"), DeclarationHandle.Create(Prefix + "card_le_theta"),
                H("The maximum bounds each eligible set"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cardinality of every three-chain-free subset is at most theta."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sweep-construction"), DeclarationHandle.Create(Prefix + "exists_sweep_theta"),
                H("A sweep system with theta orders"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A chain cover of the product with the two-element chain supplies the orders. In each chain, lower-layer points come first in reverse order, then upper-layer points in forward order, then the remaining points. A point in both layers is automatically first in its lower-layer block. Convexity prevents an interval omitting y from containing points both strictly below and strictly above y. The two layers therefore supply the required order for every interval and outsider."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sweep-dimension"), DeclarationHandle.Create(Prefix + "sweepDimension"),
                H("The minimum size of a sweep system"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Sweep dimension is the least natural number k admitting a k-order sweep system, following Boldi–Vigna, Definition 1. The orders are arbitrary linear orders, repetitions are allowed, and every order-convex subset is an interval, including the empty and full subsets. This formalization also includes empty and singleton carriers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("identity"), DeclarationHandle.Create(Prefix + "sweepDimension_eq_theta"),
                H("Sweep dimension equals theta"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite poset, sweep dimension is exactly theta. The construction gives the upper bound, and the convex-hull injection gives the lower bound. For carriers with at least two points this is the general identity used in the endpoint classifications."))), DescribeRole.Theorem)
        )));
}
