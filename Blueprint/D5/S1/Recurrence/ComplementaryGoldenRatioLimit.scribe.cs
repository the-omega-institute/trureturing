using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class ComplementaryGoldenRatioLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complementary Kimberling sequences have golden consecutive-ratio limits.",
        H("Golden Limits for the Complementary Kimberling Sequences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kimberling-complementary-golden-limits"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ComplementaryGoldenRatioLimit."
                    + "kimberling_complementary_golden_limits"),
                H("Both complementary recurrences converge to the golden ratio"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    Frac,
                    Grp(F.Id("a"), Caret, Grp(Minus), Underscore,
                        Grp(F.Id("n"), Plus, D(1))),
                    Grp(F.Id("a"), Caret, Grp(Minus), Underscore, F.Id("n")),
                    Eq, Varphi, Sp, Land, Sp,
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    Frac,
                    Grp(F.Id("a"), Caret, Grp(Plus), Underscore,
                        Grp(F.Id("n"), Plus, D(1))),
                    Grp(F.Id("a"), Caret, Grp(Plus), Underscore, F.Id("n")),
                    Eq, Varphi))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "OEIS A293317 and A293316, entered by Clark Kimberling on "
                        + "2017-10-28, label their golden-ratio limits as Conjecture; "
                        + "this theorem proves both Conjecture limits. The minus-labelled "
                        + "sequence is A293317 and the plus-labelled sequence is A293316.")),
                    Paragraph(Text(
                        "The positive-mex construction yields positive target and "
                        + "complementary terms. Its state lengths and append structure "
                        + "give the exact recurrences, while a finite-set cardinality "
                        + "bound makes the complementary term grow at most linearly.")),
                    Paragraph(Text(
                        "A two-step growth estimate gives a geometric lower bound for the "
                        + "target term, so each signed recurrence error is negligible "
                        + "relative to the next denominator. The general perturbed "
                        + "Fibonacci ratio theorem then gives both limits. Executable "
                        + "checks reproduce both OEIS sequences through index twelve."))),
                DescribeRole.Theorem))));
}
