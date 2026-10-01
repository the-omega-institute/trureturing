using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingRoyalLowFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingRoyalLowFiber.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permitted ascent positions parametrize the avoiders of a fixed Dyck shape.",
        H("Compositions for a Fixed Dyck Shape"),
        Blocks(
            Node("nonnesting-nonnestingroyallowfiber-good-positions", "Permitted ascent positions", "goodPositions",
                "Among the indices less than n minus one, retain those for which every separation of the corresponding consecutive downsteps in d is empty or consists of a single upstep with the preceding prefix having one more upstep than downstep.", DescribeRole.Definition),
            Node("nonnesting-nonnestingroyallowfiber-low-fiber-encoding", "Fixed-shape composition equivalence", "lowFiberEncoding",
                "For a Dyck path d of semilength n, compositions of n whose increasing-block permutation has ascents only at permitted positions correspond bijectively to doubled nonnesting permutations of shape d avoiding 1132 and 2213.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
