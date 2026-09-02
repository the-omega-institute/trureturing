using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class ComplementaryGoldenRatioLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vanishing relative errors preserve golden limits in positive Fibonacci recurrences.",
        H("Golden Limits for Perturbed Fibonacci Recurrences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("perturbed-fibonacci-ratio"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/ComplementaryGoldenRatioLimit."
                    + "perturbed_fibonacci_ratio"),
                H("Vanishing relative errors preserve the golden ratio"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("e"), Colon, Sp,
                    Mathbb, Grp(F.Id("N")), To, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Open, Forall, Sp, F.Id("n"), Comma, Sp,
                    D(0), Lt, F.Id("x"), Underscore, F.Id("n"), Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("n"), Comma, Sp,
                    F.Id("x"), Underscore, Grp(F.Id("n"), Plus, D(2)), Eq,
                    F.Id("x"), Underscore, Grp(F.Id("n"), Plus, D(1)), Plus,
                    F.Id("x"), Underscore, F.Id("n"), Plus,
                    F.Id("e"), Underscore, F.Id("n"), Close, Sp, Land, Sp,
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    Frac,
                    Grp(F.Id("e"), Underscore, F.Id("n")),
                    Grp(F.Id("x"), Underscore, Grp(F.Id("n"), Plus, D(1))),
                    Eq, D(0), Sp, Implies, Sp,
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    Frac,
                    Grp(F.Id("x"), Underscore, Grp(F.Id("n"), Plus, D(1))),
                    Grp(F.Id("x"), Underscore, F.Id("n")),
                    Eq, Varphi))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "OEIS A293317 and A293316, entered by Clark Kimberling on "
                        + "2017-10-28, label their golden-ratio limits as Conjecture; "
                        + "this theorem supplies the analytic core but does not yet "
                        + "prove those two sequence-specific limits. Kimberling and "
                        + "Moses, Fibonacci Quarterly 57(5) (2019), Theorem 2.1, "
                        + "assumes that the consecutive-ratio limit exists, so it does "
                        + "not cover the missing convergence claim.")),
                    Paragraph(Text(
                        "For any positive real recurrence obtained from the Fibonacci "
                        + "recurrence by a signed error, if that error divided by the "
                        + "next denominator tends to zero, then consecutive ratios tend "
                        + "to the golden ratio. The proof traps the ratios in a positive "
                        + "compact interval and combines contraction of x maps to "
                        + "one plus one over x with a local vanishing-affine-error lemma.")),
                    Paragraph(Text(
                        "The executable positive-mex definitions in the same Lean module "
                        + "reproduce both OEIS sequences through index twelve. Closing "
                        + "the two conjectures still requires the unproved structural "
                        + "bridge: complementarity and monotonicity, a linear bound for "
                        + "the complementary sequence, and Fibonacci domination of the "
                        + "target sequence."))),
                DescribeRole.Theorem))));
}
