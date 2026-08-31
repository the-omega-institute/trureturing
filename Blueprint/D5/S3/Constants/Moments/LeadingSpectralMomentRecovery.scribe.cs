using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class LeadingSpectralMomentRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading positive spectral scale and its positive inverse-square ordinate are recovered from power moments.",
        H("Leading Spectral Moment Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leading-spectral-moment-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Moments/LeadingSpectralMomentRecovery."
                        + "leading_spectral_moment_recovery"),
                H("Power moments recover the leading spectral scale"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let alpha be a strictly decreasing positive real spectrum, let "
                            + "multiplicity assign natural multiplicities, and assume the "
                            + "multiplicity-weighted first spectral powers are summable. The "
                            + "leading multiplicity and the inverse-square ordinate gamma are "
                            + "positive, with alpha at zero equal to the square of gamma inverse.")),
                    Paragraph(Text(
                        "Define each moment as the infinite sum of multiplicity times the "
                            + "corresponding spectral power. Dominated convergence makes the "
                            + "normalized tail tend to the leading multiplicity. Consecutive "
                            + "moment ratios and real roots therefore recover alpha at zero, "
                            + "while the square root of the inverse ratio recovers gamma.")),
                    Paragraph(Text(
                        "Repository, pinned library, and external Lean searches found no equal "
                            + "or stronger leading-atom moment theorem. The proof directly uses "
                            + "the pinned dominated-convergence theorem for infinite sums, the "
                            + "power limit below one, real-power continuity, division, and "
                            + "square-root continuity."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula alpha = F.Id("alpha");
        Formula multiplicity = F.Id("multiplicity");
        Formula gamma = F.Id("gamma");
        Formula j = F.Id("j");
        Formula n = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula alphaZero = Call("alpha", D(0));
        Formula multiplicityZero = Call("multiplicity", D(0));
        Formula realMultiplicity = Call("real", Call("multiplicity", j));
        Formula alphaAtJ = Call("alpha", j);
        Formula summand = Seq(
            realMultiplicity, Sp, Times, Sp,
            new Formula.Power(alphaAtJ, Seq(n, Sp, Plus, Sp, D(1))));
        Formula momentAtN = Call("moment", n);
        Formula momentDefinition = Seq(
            F.Id("moment"), Colon, Sp, naturals, Sp, To, Sp, reals,
            Sp, Colon, Eq, Sp,
            Open, n, Colon, Sp, naturals, Sp, Mapsto, Sp,
            Call("tsum", j, summand), Close);
        Formula nextN = Seq(n, Sp, Plus, Sp, D(1));
        Formula momentNext = Call("moment", nextN);
        Formula ratio = new Formula.Fraction(momentNext, momentAtN);
        Formula rootExponent = new Formula.Fraction(
            D(1), Call("real", Seq(n, Sp, Plus, Sp, D(1))));
        Formula momentRoot = Seq(momentAtN, Caret, Grp(rootExponent));
        Formula inverseRatioRoot = Seq(
            Sqrt, Grp(new Formula.Fraction(momentAtN, momentNext)));
        Formula alphaGamma = Seq(
            alphaZero, Sp, Eq, Sp,
            Open, gamma, Caret, Grp(Minus, D(1)), Close,
            Caret, Grp(D(2)));

        Formula ratioLimit = Call(
            "Tendsto",
            Seq(Open, n, Sp, Mapsto, Sp, ratio, Close),
            F.Id("atTop"),
            Call("nhds", alphaZero));
        Formula rootLimit = Call(
            "Tendsto",
            Seq(Open, n, Sp, Mapsto, Sp, momentRoot, Close),
            F.Id("atTop"),
            Call("nhds", alphaZero));
        Formula ordinateLimit = Call(
            "Tendsto",
            Seq(Open, n, Sp, Mapsto, Sp, inverseRatioRoot, Close),
            F.Id("atTop"),
            Call("nhds", gamma));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            alpha, Colon, Sp, naturals, Sp, To, Sp, reals, Comma, Sp,
            multiplicity, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            gamma, Sp, InMacro, Sp, reals, Comma, RowBreak, Grp(),
            Open, Forall, Sp, j, Sp, InMacro, Sp, naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, Call("alpha", j), Close, Sp, Land, Sp,
            Call("StrictAnti", alpha), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, multiplicityZero, Sp, Land, RowBreak, Grp(),
            Call(
                "Summable",
                Seq(Open, j, Sp, Mapsto, Sp,
                    realMultiplicity, Sp, Times, Sp, alphaAtJ, Close)),
            Sp, Land, Sp,
            D(0), Sp, Lt, Sp, gamma, Sp, Land, Sp,
            alphaGamma, Sp, Rightarrow, RowBreak, Grp(),
            F.Text, Grp(F.Id("let"), Sp), Sp,
            momentDefinition, Semi, RowBreak, Grp(),
            ratioLimit, Sp, Land, RowBreak, Grp(),
            rootLimit, Sp, Land, RowBreak, Grp(),
            ordinateLimit, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
