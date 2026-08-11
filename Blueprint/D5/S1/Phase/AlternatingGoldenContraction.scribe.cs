using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class AlternatingGoldenContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Golden negative-axis steps alternate and contract toward the center minus one.",
        H("Alternating Golden Contraction"),
        Blocks(
            Describe.Lean(DescribeId.Create("alternating-golden-contraction-tends-to-minus-one"),
                DeclarationHandle.Create("D5/S1/Phase/AlternatingGoldenContraction.alternating_golden_contraction_tendsto"),
                H("Every alternating golden orbit tends to minus one"),
                StatementSource.FromAuthor(Disp(Seq(
                                    F.Id("G"), Open, F.Id("x"), Close, Eq, Minus, D(1), Minus,
                                    Frac, Grp(F.Id("x"), Plus, D(1)), Grp(Varphi, Caret, D(3)),
                                    Comma, Quad, Sp, Lim, Underscore, Grp(F.Id("n"), To, Infty),
                                    F.Id("G"), Caret, Grp(F.Id("n")), Open, F.Id("x"), Close,
                                    Eq, Minus, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Center an affine real recurrence at minus one. Each step reverses "
                                        + "the centered displacement and divides its magnitude by the cube "
                                        + "of the golden ratio. For every real starting point, the iterated "
                                        + "recurrence converges to minus one. The private closed-form lemma "
                                        + "also records the alternating geometric displacement after every "
                                        + "finite number of steps, so the limit is derived from the exact "
                                        + "dynamics rather than assumed.")),
                                    Paragraph(Text(
                                        "Pinned Mathlib supplies `Real.one_lt_goldenRatio` and "
                                        + "`tendsto_pow_atTop_nhds_zero_of_abs_lt_one`. A source search "
                                        + "found no declaration for this affine golden iteration or its "
                                        + "closed form, so the result is a new short proof assembled around "
                                        + "the library's geometric-power limit rather than a thin wrapper. "
                                        + "The approximate finite readings in the source atom motivate the "
                                        + "claim but are not used as hypotheses or numerical certificates."))),
                DescribeRole.Theorem))));
}
