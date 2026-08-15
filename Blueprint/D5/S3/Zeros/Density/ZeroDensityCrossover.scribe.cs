using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Density;

internal sealed class ZeroDensityCrossoverDocument : IScribeDocumentDefinition
{
    private static Formula HalfMinusEpsilon() => Seq(
        Open, Frac, Grp(D(1)), Grp(D(2)), Sp, Minus, Sp, Varepsilon, Close);

    private static Formula InghamExponent() => Seq(
        Frac,
        Grp(D(3), Sp, HalfMinusEpsilon()),
        Grp(Frac, Grp(D(3)), Grp(D(2)), Sp, Minus, Sp, Varepsilon));

    private static Formula HuxleyExponent() => Seq(
        Frac,
        Grp(D(3), Sp, HalfMinusEpsilon()),
        Grp(Frac, Grp(D(1)), Grp(D(2)), Sp, Plus, Sp, D(3), Varepsilon));

    private static Formula GuthMaynardExponent() => Seq(
        Frac, Grp(D(3, 0), Sp, HalfMinusEpsilon()), Grp(D(1, 3)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Guth-Maynard density exponent wins exactly between the two classical crossovers.",
        H("Zero-Density Exponent Crossover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("guth-maynard-dominates-exactly-between-crossovers"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Density/ZeroDensityCrossover.guth_maynard_dominates_iff"),
                H("The Guth-Maynard exponent dominates exactly on the crossover interval"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Varepsilon, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Sp, Leq, Sp, Varepsilon, Sp, Lt, Sp,
                    Frac, Grp(D(1)), Grp(D(2)), Comma, Esc,
                    Open,
                    GuthMaynardExponent(), Sp, Leq, Sp, InghamExponent(), Sp, Land, Sp,
                    GuthMaynardExponent(), Sp, Leq, Sp, HuxleyExponent(),
                    Close, Sp, Leftrightarrow, Sp,
                    Open,
                    Frac, Grp(D(1)), Grp(D(5)), Sp, Leq, Sp, Varepsilon, Sp, Land, Sp,
                    Varepsilon, Sp, Leq, Sp, Frac, Grp(D(4)), Grp(D(1, 5)),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source records the Ingham, Huxley, and Guth-Maynard zero-density "
                        + "exponents. After writing the depth as epsilon = sigma - 1/2, their two "
                        + "exact crossover points are epsilon = 1/5 and epsilon = 4/15.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies div_le_div_iff0 for positive denominators. The "
                        + "Lean proof checks positivity on 0 <= epsilon < 1/2, applies that library "
                        + "equivalence to both comparisons, and closes the resulting polynomial "
                        + "inequalities.")),
                    Paragraph(Text(
                        "This theorem closes only the exact algebraic comparison of the three "
                        + "displayed exponent formulas. It does not prove the analytic zero-density "
                        + "estimates themselves, the numerical census table, or any stated RH or "
                        + "Lindelof consequence."))),
                DescribeRole.Theorem)),
        []));
}
