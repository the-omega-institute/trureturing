using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateCycleReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleReduction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first two fundamental images of the distinguished cycle reduce avoidance to conditions on the parameter.",
        H("Reduction along the Distinguished Cycle"),
        Blocks(
            Node("fundamental-bijection-thetaiteratecyclereduction-p-cycle-reduction", "Images and avoidance of the cycle family", "P_cycle_reduction",
                "For a nonempty parameter permutation r of length h, the first image of P(r) is h plus two followed by r increased by one and then one, and the second image is the fundamental image of r increased by one followed by h plus two and one. Avoidance through the second iterate is equivalent to 132-avoidance of r, its fundamental image and b(r), together with the absence of an increasing positional pair in b(r) straddling the first value of r plus one. The first and last values of P(r) are h plus two and the first value of r plus one, and its values at positions labelled by r are the corresponding shifted successors.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
