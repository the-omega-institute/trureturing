using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenNineClassicalSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenNineClassicalSplit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathematical definitions and results for Fishburn permutations and classical pattern avoidance.",
        H("FishburnTenNineClassicalSplit"),
        Blocks(
            Node("fishburntennineclassicalsplit-avoids231-maxsplit-iff-theorem", "Theorem avoids231_maxSplit_iff", "avoids231_maxSplit_iff", "This theorem establishes the stated mathematical relation for Fishburn permutations and classical pattern avoidance.", DescribeRole.Theorem),
            Node("fishburntennineclassicalsplit-avoids4123-maxsplit-iff-theorem", "Theorem avoids4123_maxSplit_iff", "avoids4123_maxSplit_iff", "This theorem establishes the stated mathematical relation for Fishburn permutations and classical pattern avoidance.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
