using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenAuxiliaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations avoiding 213 decompose at their first entry and their maximum.",
        H("FishburnTenSevenAuxiliary"),
        Blocks(
            Node("fishburntensevenauxiliary-h-head-decomposition-theorem", "Decomposition at the first entry", "H_head_decomposition",
                "A list is a Fishburn permutation of length size plus one avoiding 213 if and only if there is a Fishburn permutation q of length size avoiding 213 such that the list is either size plus one followed by q, or one followed by q with every entry increased by one.", DescribeRole.Theorem),
            Node("fishburntensevenauxiliary-h-maximum-equiv-definition", "Decomposition at the maximum", "H_maximum_equiv",
                "For every positive size, this bijection identifies Fishburn permutations of length size avoiding 213 with pairs consisting of a cut from zero through size minus one and a Fishburn permutation of length size minus cut minus one avoiding 213.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
