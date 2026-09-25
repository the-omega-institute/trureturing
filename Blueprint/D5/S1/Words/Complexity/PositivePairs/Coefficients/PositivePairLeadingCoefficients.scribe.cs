using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Coefficients;

internal sealed class PositivePairsCoefficientsPositivePairLeadingCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successor positive pairs have the actual leading commutator coefficients.",
        H("PositivePairLeadingCoefficients"),
        Blocks(
            Paragraph(Text(
                "Magnus expansions and shuffle or infiltration identities are classical context, "
                + "but the complete recursively indexed positive-pair construction below is a "
                + "repository route. Indices are retained even when two evaluated pairs coincide.")),
            D("successor-leading-bracket", "full_positivePair_successor_leading_bracket", "Successor difference is a commutator",
                "For finite A with decidable equality and index at level r+2, let c be the preceding actual cutoff-Magnus difference and x the rationalized abelianization of the previous right word plus X_a. The successor Magnus difference equals cutoffMul c x - cutoffMul x c in cutoff r+2."),
            D("successor-ratio-leading-bracket", "full_positivePair_successor_ratio_leading_bracket", "The ratio has the same leading commutator",
                "Under the same hypotheses and definitions, positivePairRatio at level and cutoff r+2 minus cutoffOne equals cutoffMul c x - cutoffMul x c."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
