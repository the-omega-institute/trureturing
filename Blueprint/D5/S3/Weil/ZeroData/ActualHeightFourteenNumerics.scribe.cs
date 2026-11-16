using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualHeightFourteenNumericsDocument : IScribeDocumentDefinition
{
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Q(long s) => Call("Re", Div(
        new Formula.Negate(Call("deriv", DefinitionDsl.Id("riemannZeta"), N(s))), Call("riemannZeta", N(s))));

    private static Formula Estimate()
    {
        var value = Add(Div(N(66493177), N(143006288128704000)),
            Mul(Div(N(4), N(12649365729)), DefinitionDsl.Id("EulerGamma")));
        value = Sub(value, Div(Call("log", N(2)), N(1816214400)));
        value = Sub(value, Mul(Div(N(9487), N(40477970332800)), Call("log", Pi)));
        value = Add(value, Div(Q(6), N(3990729600)));
        value = Sub(value, Div(Q(8), N(3555377280)));
        value = Add(value, Div(Q(10), N(6739588800)));
        value = Sub(value, Div(Q(12), N(24711825600)));
        value = Add(value, Div(Q(14), N(216459734400)));
        var upper = Div(N(72126772613108177), Mul(N(151944181136748), new Formula.Power(N(10), N(17))));
        return new Formula.Relation(value, FormulaRelationOperator.LessThanOrEqual, upper);
    }

    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Then(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Bounds()
    {
        var rho = DefinitionDsl.Id("rho");
        var real = Call("re", rho);
        var square = new Formula.Power(Call("im", rho), N(2));
        var weight = Call("h14Weight", rho);
        var denominator = Add(Mul(N(72636), new Formula.Power(N(10), N(18))), N(763553532703907200));
        var lower = Div(N(345650537), denominator);
        var conclusion = new Formula.Logic(Less(N(0), weight), FormulaLogicOperator.And,
            Then(Le(square, N(196)), Le(lower, Mul(N(2), weight))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("rho"),
            Seq(Mathbb, Grp(FormulaDsl.Id("C"))),
            Then(Less(N(0), real), Then(Less(real, N(1)), Then(Less(N(100), square), conclusion))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete Signed Zeta Resolvent Estimate",
        H("Complete Signed Zeta Resolvent Estimate"),
        Blocks(Describe.Lean(
            DescribeId.Create("actualheightfourteennumerics"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_evaluatedMass_upper"),
            H("Complete Signed Zeta Resolvent Estimate"), StatementSource.FromAuthor(Disp(Estimate())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The complete von Mangoldt series is split at 64. Every omitted term is retained: positive coefficients use the integral tail, and negative coefficients use nonnegativity. Rational logarithm and Euler constant bounds yield the exact signed scalar upper bound consumed by h14Mass_upper and actual_height_gt_fourteen. The first Li mass is supplied by the original owner, and no height or mass conclusion is a premise."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("actualheightfourteennumericskernel"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_kernel_bounds"),
            H("Concrete six-pole kernel bounds"), StatementSource.FromAuthor(Disp(Bounds())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The six shifts 0, 30, 56, 90, 132, and 182 are now consumed in this numerical owner. The generic Sector calculus supplies positivity and monotonicity; the exact six-pole evaluation gives the full lower constant with every sign and multiplicity preserved. The open-strip and height-ten premises are discharged by the existing complete zero-data source."))),
            DescribeRole.Theorem))));
}
