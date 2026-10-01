using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingRoyalLowGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowGap.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance of 1132 and 2213 restricts the gaps between consecutive downsteps at ascents.",
        H("Necessary Gaps at Ascents"),
        Blocks(
            Node("nonnesting-nonnestingroyallowgap-ascent-forces-good-gap", "Necessity of the gap condition", "ascent_forces_good_gap",
                "Let a doubled nonnesting word avoid 1132 and 2213, have Dyck shape d, and have the same distinct-letter order p at its upsteps and downsteps. If consecutive downsteps correspond to an ascent of p, then the intervening sequence is empty or is a single upstep with the preceding prefix having one more upstep than downstep.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
