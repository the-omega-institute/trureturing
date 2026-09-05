using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GermWindow;

internal sealed class GermZeroCertificateJetDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/GermWindow/GermZeroCertificateJet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This is layer L2a of the G-c certificate in 增订三十四: it unconditionally "
            + "discharges the third center-jet hypothesis of germ_zero_of_center_jet "
            + "by proving curvature at most 400 throughout Q, certifies log 2 to "
            + "2^{-60}, and proves the v <= 1 prefix of the derivative real-part bound.",
        H("Golden Germ Zero Certificate: Curvature and First-Mode Jet"),
        Blocks(
            Entry(
                "binary-logarithm-rational-approximation",
                "logTwoApprox",
                LogTwoApproxFormula(),
                "The rational 60-term approximation to log 2",
                "The named rational constant is the first sixty terms of the binary logarithm series.",
                DescribeRole.Definition),
            Entry(
                "binary-logarithm-series-error",
                "log_two_binary_60_sum",
                LogTwoBinarySumFormula(),
                "The explicit 60-term series certifies log 2 to 2^{-60}",
                "The pinned geometric-series remainder theorem gives the error bound for the displayed real series.",
                DescribeRole.Theorem),
            Entry(
                "binary-logarithm-error",
                "log_two_binary_60",
                LogTwoBinaryFormula(),
                "The rational approximation certifies log 2 to 2^{-60}",
                "The geometric-series remainder bounds the error of logTwoApprox by one part in 2^{60}.",
                DescribeRole.Theorem),
            Entry(
                "first-mode-derivative-real-part",
                "g1_deriv_re_gt_one",
                FirstModeDerivativeFormula(),
                "The first nonconstant mode has derivative real part greater than one",
                "A certified reduction of the mode-one phase modulo 3 pi, together with explicit cosine and decay bounds, proves the v <= 1 prefix.",
                DescribeRole.Theorem),
            Entry(
                "sixty-mode-curvature-118",
                "g60_curvature_le_118",
                CurvatureFormula(F.D(1, 1, 8)),
                "The 61-mode curvature is at most 118 on Q",
                "The mode-wise second-derivative identity and a rational geometric majorant give the uniform bound 118.",
                DescribeRole.Theorem),
            Entry(
                "sixty-mode-curvature-400",
                "g60_curvature_le",
                CurvatureFormula(F.D(4, 0, 0)),
                "The layer-1 curvature hypothesis holds on Q",
                "The sharper bound 118 implies the required bound 400, discharging the third center-jet hypothesis of germ_zero_of_center_jet unconditionally on Q. The full inequalities 187/100 < Re(g_60'(c)) and ||g_60(c)|| < 4*10^{-10} belong to L2c and are not claimed here. This module makes no claim about RH.",
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/GermWindow/GermZeroCertificateReduction")),
        ]));

    private static DocumentBlock.Describe Entry(
        string id,
        string declaration,
        Formula statement,
        string title,
        string prose,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula LogTwoApproxFormula()
    {
        Formula i = F.Id("i");
        Formula index = Add(i, F.D(1));
        Formula term = Fraction(
            Power(F.Seq(F.Grp(Fraction(F.D(1), F.D(2)))), F.Seq(index)),
            index);
        Formula sum = F.Seq(
            F.Sum,
            F.Underscore,
            F.Grp(F.Seq(i, F.Eq, F.D(0))),
            F.Caret,
            F.Grp(F.D(5, 9)),
            term);
        return Disp(Equal(F.Id("logTwoApprox"), sum));
    }

    private static Formula LogTwoBinaryFormula() =>
        Disp(LessOrEqual(
            new Formula.Absolute(Subtract(
                Call("log", F.D(2)),
                F.Id("logTwoApprox"))),
            Fraction(F.D(1), Power(F.Seq(F.D(2)), F.D(6, 0)))));

    private static Formula LogTwoBinarySumFormula()
    {
        Formula i = F.Id("i");
        Formula index = Add(i, F.D(1));
        Formula term = Fraction(
            Power(F.Seq(F.Grp(Fraction(F.D(1), F.D(2)))), F.Seq(index)),
            index);
        Formula sum = F.Seq(
            F.Sum,
            F.Underscore,
            F.Grp(F.Seq(i, F.Eq, F.D(0))),
            F.Caret,
            F.Grp(F.D(5, 9)),
            term);
        return Disp(LessOrEqual(
            new Formula.Absolute(Subtract(Call("log", F.D(2)), sum)),
            Power(F.Seq(F.Grp(Fraction(F.D(1), F.D(2)))), F.D(6, 0))));
    }

    private static Formula FirstModeDerivativeFormula() =>
        Disp(Less(
            F.D(1),
            RealPart(Call("deriv", Call("g", F.D(1)), F.Id("c")))));

    private static Formula CurvatureFormula(Formula bound)
    {
        Formula s = F.Id("s");
        Formula secondDerivative = Call(
            "deriv",
            Call("deriv", Call("g", F.D(6, 0))),
            s);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(
                Member(s, F.Id("Q")),
                LessOrEqual(new Formula.Norm(secondDerivative), bound))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Grp(value));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));
}
