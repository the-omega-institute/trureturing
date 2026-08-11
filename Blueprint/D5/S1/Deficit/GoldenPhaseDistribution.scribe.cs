using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class GoldenPhaseDistributionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Uniform golden phases give the exact three-valued deficit frequencies and mean.",
        H("Golden Phase Deficit Distribution"),
        Blocks(
            Describe.Lean(DescribeId.Create("golden-phase-deficit-distribution"),
                DeclarationHandle.Create("D5/S1/Deficit/GoldenPhaseDistribution.limiting_deficit_distribution"),
                H("Uniform golden phase sampling has exact deficit frequencies"),
                StatementSource.FromAuthor(DistributionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The positive and negative events are the two corner triangles cut "
                                        + "from the unit phase square by the deficit thresholds. Their legs "
                                        + "have lengths inverse golden ratio and inverse golden ratio squared. "
                                        + "Integrating the vertical cross sections gives one half times the "
                                        + "square of each leg. The signed expectation is the positive area "
                                        + "minus the negative area, which simplifies by the golden quadratic "
                                        + "identity to one over twice the golden ratio cubed."))),
                DescribeRole.Theorem)),
        []));

    private static Formula DistributionFormula() =>
        Disp(Seq(
            F.Id("freq"), Open, Plus, D(1), Close, Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(2), F.Id("phi"), Caret, Grp(D(2))), Comma, Sp,
            F.Id("freq"), Open, Minus, D(1), Close, Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(2), F.Id("phi"), Caret, Grp(D(4))), Comma, Sp,
            F.Id("E"), Open, F.Id("c"), Close, Sp, Eq, Sp,
            Frac, Grp(D(1)), Grp(D(2), F.Id("phi"), Caret, Grp(D(3)))));
}
