using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Coefficients;

internal sealed class PositivePairsCoefficientsPositivePairFiltrationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full indexed positive-pair family has the required cutoff filtration.",
        H("PositivePairFiltration"),
        Blocks(
            Paragraph(Text(
                "Magnus expansions and shuffle or infiltration identities are classical context, "
                + "but the complete recursively indexed positive-pair construction below is a "
                + "repository route. Indices are retained even when two evaluated pairs coincide.")),
            D("positive-pair-index", "PositivePairIndex", "Full recursive choice index",
                "PositivePairIndex A r abbreviates Fin r -> A. Distinct indices remain distinct even if their evaluated word pairs coincide.", DescribeRole.Definition),
            D("positive-pair-words", "positivePairWords", "Actual recursive positive pairs",
                "Level zero is ([],[]), level one is ([a],[]), and a successor step sends (u,v) and a to (u++[a]++v, v++[a]++u).", DescribeRole.Definition),
            D("cutoff-magnus", "cutoffMagnus", "Actual Magnus cutoff",
                "For finite A, cutoffMagnus r source is the rational coefficient extension of the actual Magnus polynomial restricted through degree r.", DescribeRole.Definition),
            D("positive-pair-ratio", "positivePairRatio", "Actual positive-pair Magnus ratio",
                "For independent cutoff and level parameters, positivePairRatio is cutoffMagnus(u) multiplied by the finite geometric inverse of cutoffMagnus(v)-1 for the actual pair (u,v).", DescribeRole.Definition),
            D("positive-pair-ratio-filtration", "full_positivePair_ratio_filtration", "Full indexed family agrees below its level",
                "For every finite alphabet, cutoff, level r, and full PositivePairIndex, both the actual cutoff-Magnus difference M(u)-M(v) and the ratio minus one vanish below r. Duplicate pairs and zero leading directions remain in the quantified family."),
            D("cutoff-magnus-cancellation", "cutoffMagnus_cancellation", "Cancellation of actual cutoff Magnus factors",
                "The empty-word coefficient of every actual Magnus image is one. Finite geometric inverses in the truncated split-convolution algebra therefore cancel common left factors and equal right factors in appended positive words at every cutoff."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
