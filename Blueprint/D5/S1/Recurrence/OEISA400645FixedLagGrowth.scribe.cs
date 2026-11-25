using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class OEISA400645FixedLagGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/OEISA400645FixedLagGrowth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a400645siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every A400645 source sequence has fixed-lag ratios tending to λ^h and logarithmic "
            + "growth rate log λ.",
        H("Fixed-lag and logarithmic growth for A400645"),
        Blocks(
            Describe.Lean(DescribeId.Create("a400645-fixed-lag-growth"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Fixed-lag ratios and logarithmic growth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let a be any sequence satisfying the A400645 source conditions, and let "
                    + "λ be the limiting ratio of the frozen A400645 module. For every fixed "
                    + "h ≥ 0, including h = 0, a_{n+h}/a_n tends to λ^h, and log(a_n)/n tends "
                    + "to log λ. The frozen theorem gives eventual positivity and "
                    + "a_{n+1}/a_n → λ. Multiplying h consecutive ratios gives the first limit "
                    + "by induction on h. For the second, the logarithms of the consecutive "
                    + "ratios tend to log λ, since λ > 0. Choose N with a_n > 0 for n ≥ N. "
                    + "From index N the partial sums telescope to log a_{n+N} − log a_N, and "
                    + "the Cesàro mean of a convergent sequence has the same limit; rescaling "
                    + "by n/(n+N) → 1 and shifting the index give the second limit. This is "
                    + "Corollary 6 of H. Ma and W. Zhang's note "
                    + "(DOI 10.5281/zenodo.24369110)."))),
                DescribeRole.Theorem))));
}
