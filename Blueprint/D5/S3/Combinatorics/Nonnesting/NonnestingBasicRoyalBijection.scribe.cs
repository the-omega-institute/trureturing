using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalBijectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalBijection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A permutation and a Dyck path specify a doubled nonnesting permutation.",
        H("Permutation and Dyck-Path Encoding"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalbijection-royal-pairs", "Permutation and path pairs", "royalPairs",
                "A pair consists of a permutation of the letters from one through n and a Dyck path whose semilength equals the length of that permutation.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicroyalbijection-royal-encoding", "Interleaving equivalence", "royalEncoding",
                "Pairs of a permutation of one through n and a Dyck path of semilength n correspond bijectively to doubled nonnesting permutations. Read the permutation once along the upsteps and once along the downsteps.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
