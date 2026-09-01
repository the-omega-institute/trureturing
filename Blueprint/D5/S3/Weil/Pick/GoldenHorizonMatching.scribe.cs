using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class GoldenHorizonMatchingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Pick/GoldenHorizonMatching.golden_horizon_matching";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden effective index characterizes six equivalent rank-one channel conditions.",
        H("Golden Horizon Matching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-effective-index-characterizes-rank-one-channel-data"),
                DeclarationHandle.Create(Declaration),
                H("The golden effective index characterizes rank-one channel data"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive frequencies with omega strictly below delta, sigma is the "
                            + "positive contraction ratio omega/delta. The theorem constructs the "
                            + "single-entry real Hankel matrix and uses its canonical frozen "
                            + "effective index.")),
                    Paragraph(Text(
                        "The rapidity is artanh(sigma), with the standard real Bogoliubov "
                            + "coefficients cosh and sinh. The logarithmic divergence is the "
                            + "natural logarithm of the effective index.")),
                    Paragraph(Text(
                        "All seven source conditions are public: six biconditionals connect the "
                            + "golden index value to the defect, squared contraction ratio, two "
                            + "coefficient magnitudes, logarithmic divergence, and frequency ratio."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula delta = DeltaLower;
        Formula omega = Omega;
        Formula sigma = SigmaLower;
        Formula hankel = F.Id("H");
        Formula index = Seq(F.Id("I"), Underscore, Grp(F.Id("hor")));
        Formula rapidity = F.Id("r");
        Formula alpha = Alpha;
        Formula beta = Beta;
        Formula divergence = Seq(F.Id("D"), Underscore, Grp(F.Id("KL")));
        Formula phiSquared = Pow(Varphi, D(2));
        Formula phiInverse = Pow(Varphi, Seq(Minus, D(1)));
        Formula indexGolden = Equal(index, phiSquared);

        Formula assumptions = Seq(
            D(0), Sp, Lt, Sp, delta, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, omega, Sp, Land, Sp,
            omega, Sp, Lt, Sp, delta);

        Formula defectCondition = Equal(
            Seq(D(1), Sp, Minus, Sp, Pow(sigma, D(2))),
            Pow(Varphi, Seq(Minus, D(2))));
        Formula contractionCondition = Equal(Pow(sigma, D(2)), phiInverse);
        Formula alphaCondition = Equal(
            Seq(new Formula.Absolute(alpha), Caret, Grp(D(2))),
            phiSquared);
        Formula betaCondition = Equal(
            Seq(new Formula.Absolute(beta), Caret, Grp(D(2))),
            Varphi);
        Formula divergenceCondition = Equal(
            divergence,
            Seq(D(2), Sp, Times, Sp, Call("log", Varphi)));
        Formula ratioCondition = Equal(
            new Formula.Fraction(omega, delta),
            Seq(Sqrt, Grp(phiInverse)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, delta, Sp, InMacro, Sp, real, Comma, Sp,
                omega, Sp, InMacro, Sp, real, Comma),
            Seq(Grp(), assumptions, Sp, Rightarrow),
            Let(sigma, new Formula.Fraction(omega, delta)),
            LetTyped(
                hankel,
                Pow(real, Seq(D(1), Sp, Times, Sp, D(1))),
                Call("matrix1x1", sigma)),
            Let(index, Call("horizonEffectiveIndex", hankel)),
            Let(rapidity, Call("artanh", sigma)),
            Let(alpha, Call("cosh", rapidity)),
            Let(beta, Call("sinh", rapidity)),
            Let(divergence, Call("log", index)),
            Seq(Grp(), Open, IffFormula(indexGolden, defectCondition), Close, Sp, Land),
            Seq(Grp(), Open, IffFormula(indexGolden, contractionCondition), Close, Sp, Land),
            Seq(Grp(), Open, IffFormula(indexGolden, alphaCondition), Close, Sp, Land),
            Seq(Grp(), Open, IffFormula(indexGolden, betaCondition), Close, Sp, Land),
            Seq(Grp(), Open, IffFormula(indexGolden, divergenceCondition), Close, Sp, Land),
            Seq(Grp(), Open, IffFormula(indexGolden, ratioCondition), Close, Dot),
        ]));
    }

    private static Formula Let(Formula name, Formula value) =>
        Seq(Grp(), F.Id("let"), Sp, name, Sp, Eq, Sp, value, Semi);

    private static Formula LetTyped(Formula name, Formula type, Formula value) =>
        Seq(
            Grp(), F.Id("let"), Sp, name, Colon, Sp, type,
            Sp, Eq, Sp, value, Semi);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
