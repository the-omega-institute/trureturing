using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaBasicSumIndecompDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumIndecomp.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For 312- and 231-avoiders, indecomposability is characterized by an extreme endpoint.",
        H("Indecomposability of Pattern Avoiders"),
        Blocks(
            Node("fundamental-bijection-thetabasicsumindecomp-avoid312-indecomp-iff-last-one", "Indecomposable 312-avoiders", "avoid312_indecomp_iff_last_one",
                "A nonempty 312-avoiding permutation is sum-indecomposable exactly when its last entry is one.", DescribeRole.Theorem),
            Node("fundamental-bijection-thetabasicsumindecomp-avoid231-indecomp-iff-first-max", "Indecomposable 231-avoiders", "avoid231_indecomp_iff_first_max",
                "A nonempty 231-avoiding permutation is sum-indecomposable exactly when its first entry is its maximum.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
