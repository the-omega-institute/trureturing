using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingRoyalLowConverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowConverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The increasing-block order and permitted Dyck gaps imply avoidance of 1132 and 2213.",
        H("Avoidance from Permitted Gaps"),
        Blocks(
            Node("nonnesting-nonnestingroyallowconverse-good-gaps-avoid-low", "Sufficiency of the gap condition", "good_gaps_avoid_low",
                "Let a doubled nonnesting word have Dyck shape d and the same distinct-letter order p at its upsteps and downsteps. Suppose p avoids 132 and 213. Whenever consecutive downsteps in d correspond to an ascent of p, require either that they are adjacent or that they enclose a single upstep with the preceding prefix having one more upstep than downstep. Then the word avoids 1132 and 2213.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
