using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class BosonicRenyiStieltjesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/BosonicRenyiStieltjes";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/camilolandieliens2019renyissa");

    private static Formula X(string name) => name switch
    {
        "α" => Alpha, "ν" => Nu, "ι" => Iota, "Ω" => Omega, "θ" => Theta,
        _ => F.Id(name),
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Local(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), Reals()), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), Reals()), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula LogOf(Formula value) => At(Qualified("Real", "log"), value);
    private static Formula Angle => Mul(Qualified("Real", "pi"), Alpha);
    private static Formula SinAngle => At(Qualified("Real", "sin"), Angle);
    private static Formula CosAngle => At(Qualified("Real", "cos"), Angle);
    private static Formula OrderRange(Formula body) => Imp(LT(D(0), Alpha),
        Imp(LT(Alpha, D(2)), Imp(NE(Alpha, D(1)), body)));
    private static Formula Ioo01 => At(Qualified("Set", "Ioo"), Typed(D(0), Reals()), D(1));
    private static Formula Integrable(Formula function, Formula domain) =>
        At(Qualified("MeasureTheory", "IntegrableOn"), function, domain, Qualified("MeasureTheory", "volume"));
    private static Formula Integral(string variable, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Int, Seq(Typed(X(variable), Reals()), Sp, InMacro, Sp, domain)),
        Sp, Parenthesized(body), Thin, F.Id("d"), X(variable));

    private static Formula FunctionDefinition() => All("α", All("ν",
        Equal(Typed(Local("renyiFunction", Alpha, Nu), Reals()),
            Div(LogOf(Sub(Pow(Div(Add(Nu, D(1)), D(2)), Alpha),
                Pow(Div(Sub(Nu, D(1)), D(2)), Alpha))), Sub(Alpha, D(1))))));
    private static Formula ConstantDefinition() => All("α",
        Equal(Typed(Local("renyiConstant", Alpha), Reals()),
            Sub(Div(LogOf(Alpha), Sub(Alpha, D(1))), LogOf(D(2)))));
    private static Formula WeightDefinition()
    {
        Formula x = X("x");
        Formula squareGap = Sub(D(1), Pow(x, D(2)));
        Formula denominator = Mul(Mul(Qualified("Real", "pi"), Sub(Alpha, D(1))),
            Sub(Add(Pow(Add(D(1), x), Mul(D(2), Alpha)), Pow(Sub(D(1), x), Mul(D(2), Alpha))),
                Mul(Mul(D(2), Pow(squareGap, Alpha)), CosAngle)));
        Formula numerator = Mul(Mul(Mul(Negate(D(2)), Alpha), SinAngle), Pow(squareGap, Sub(Alpha, D(1))));
        return All("α", All("x", Equal(Typed(Local("renyiWeight", Alpha, x), Reals()), Div(numerator, denominator))));
    }
    private static Formula WeightPositive() => All("α", All("x", OrderRange(
        Imp(LE(D(0), X("x")), Imp(LT(X("x"), D(1)), LT(D(0), Local("renyiWeight", Alpha, X("x"))))))));
    private static Formula WeightIntegrable() => All("α", OrderRange(Integrable(Local("renyiWeight", Alpha), Ioo01)));
    private static Formula WeightMass() => All("α", OrderRange(
        Equal(Integral("x", Ioo01, Local("renyiWeight", Alpha, X("x"))), Div(D(1), D(2)))));
    private static Formula Representation()
    {
        Formula integrand = Mul(Local("renyiWeight", Alpha, X("x")), LogOf(Sub(Pow(Nu, D(2)), Pow(X("x"), D(2)))));
        return All("α", All("ν", OrderRange(Imp(LE(D(1), Nu),
            And(Integrable(LambdaOf("x", integrand), Ioo01),
                Equal(Local("renyiFunction", Alpha, Nu),
                    Add(Local("renyiConstant", Alpha), Integral("x", Ioo01, integrand))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bosonic Gaussian Renyi function is a positive logarithmic Stieltjes mixture for orders between zero and two, excluding one.",
        H("A positive logarithmic representation of bosonic Renyi entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("renyi-function"), DeclarationHandle.Create(Module + ".renyiFunction"),
                H("The single-mode entropy"), StatementSource.FromAuthor(Disp(FunctionDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The function is the logarithm of the difference of the two real powers, divided by α−1. For ν at least one and positive α different from one, this is the single-mode term in Eq. renyi_bosonic_1 of Camilo, Landi and Eliëns (RenyiGaussian_v2.tex, lines 216–220). The real logarithm and real powers give a total real-valued function also outside this entropy range."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("renyi-constant"), DeclarationHandle.Create(Module + ".renyiConstant"),
                H("The additive constant"), StatementSource.FromAuthor(Disp(ConstantDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The constant log(α)/(α−1)−log(2) fixes the asymptotic normalization of the logarithmic representation."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("renyi-weight"), DeclarationHandle.Create(Module + ".renyiWeight"),
                H("The logarithmic density"), StatementSource.FromAuthor(Disp(WeightDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The real density combines a signed sine factor with a power of 1−x² and a power Poisson denominator. Its positivity and integrability are asserted only for the order and interval ranges specified below."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weight-positive"), DeclarationHandle.Create(Module + ".weight_pos"),
                H("Strict positivity of the density"), StatementSource.FromAuthor(Disp(WeightPositive())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For 0<α<2 with α different from one, the signed sine factor is positive. Factoring the denominator into a positive power and a Poisson quadratic proves strict positivity for every 0≤x<1."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weight-integrable"), DeclarationHandle.Create(Module + ".weight_integrable"),
                H("Integrability at the endpoints"), StatementSource.FromAuthor(Disp(WeightIntegrable())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The substitutions q=(1−x)/(1+x) and p=q^α give an arctangent primitive. It is continuous at the endpoints, and its derivative on the open interval is the nonnegative density. The fundamental theorem of calculus for a nonnegative derivative proves integrability."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weight-mass"), DeclarationHandle.Create(Module + ".weight_mass"),
                H("Mass one half"), StatementSource.FromAuthor(Disp(WeightMass())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The same arctangent primitive evaluates the integral as the difference of its values at one and zero. The sine and cosine identities on each side of α=1 make this difference one half."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stieltjes-representation"), DeclarationHandle.Create(Module + ".stieltjes_representation"),
                H("The positive logarithmic representation"), StatementSource.FromAuthor(Disp(Representation())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For ν>1, the positive-axis Stieltjes transform of the power Poisson density identifies the derivative of the logarithmic integral with the derivative of the single-mode entropy. Their difference is constant; its limit at infinity is renyiConstant, using the density mass one half. Near ν=1, a logarithmic endpoint majorant is integrable. Dominated convergence therefore extends both the integrability and the identity to the pure-mode endpoint ν=1."))), DescribeRole.Theorem))));
}
