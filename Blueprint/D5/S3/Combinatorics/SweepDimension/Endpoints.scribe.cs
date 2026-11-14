using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SweepDimension;

internal sealed class SweepEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SweepDimension/Endpoints.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/boldi2026sweep");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The general finite-poset sweep identity determines exactly which posets attain either width bound.", H("Sweep dimension and its width endpoints"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The identity and both endpoint classifications"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite poset with at least two points, sweep dimension is theta. It equals the maximum of two and the width exactly when the poset is a chain or an antichain. It equals twice the width exactly when there are two disjoint antichains, each of maximum cardinality. A three-chain-free set splits into its minimal and nonminimal elements, both antichains. Equality at the upper endpoint forces both pieces to have maximum size. At the lower endpoint, a proper maximum antichain can be enlarged by any outside point without creating a strict three-chain; when width is at least two this rules out equality. Width at most one is exactly the chain case."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("boldi-vigna-general-sweep-endpoints"), ResolutionKind.Proved))
        )));
}
