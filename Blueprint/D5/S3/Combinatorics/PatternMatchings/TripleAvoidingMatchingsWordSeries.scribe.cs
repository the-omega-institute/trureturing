using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsWordSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-action decompositions determine accepted-word generating functions at all heights and both phases.",
        H("Generating functions of accepted suffixes"),
        Blocks(
            Node("bss-wordseries-finite-alphabet", "The finite action alphabet", "instFintypeAction",
                "The action alphabet is enumerated by its three distinct letters: opening, oldest and second. Every action is exactly one of these letters.", DescribeRole.Definition),
            Node("bss-wordseries-wordseries", "The suffix generating function", "wordSeries",
                "For height h and phase f, W(h,f;x) is the formal power series whose coefficient of x^l counts action words of length l accepted from that state. Here x counts individual scan actions.", DescribeRole.Definition),
            Node("bss-wordseries-word-series-recursion", "Boundary and higher-height equations", "word_series_recursion",
                "Write N_h = W(h,false;x) and T_h = W(h,true;x). Then N_0 = 1+xN_1, N_1 = xN_2+xN_0, N_2 = xN_3+2xN_1 and T_2 = xT_3+xN_1. For every h at least three, N_h = xN_{h+1}+x(N_{h-1}+T_{h-1}) and T_h = xT_{h+1}+xN_{h-1}. Finally N_0 = A(x^2), so its odd coefficients vanish and its coefficient of x^{2n} counts the P1-avoiding perfect matchings on 2n vertices.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
