using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class FermionicRenyiStieltjesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/FermionicRenyiStieltjes";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/camilolandieliens2019renyissa");

    private static Formula X(string name) => name switch
    {
        "α" => Alpha, "σ" => SigmaLower,
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
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), Reals), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), Reals), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula LogOf(Formula value) => At(Qualified("Real", "log"), value);
    private static Formula OrderRange(Formula body) => Imp(LT(D(0), Alpha), Imp(LT(Alpha, D(1)), body));
    private static Formula Ioo01 => At(Qualified("Set", "Ioo"), Typed(D(0), Reals), D(1));
    private static Formula Integrable(Formula function) =>
        At(Qualified("MeasureTheory", "IntegrableOn"), function, Ioo01, Qualified("MeasureTheory", "volume"));
    private static Formula Integral(string variable, Formula body) => Seq(
        new Formula.Subscript(Int, Seq(Typed(X(variable), Reals), Sp, InMacro, Sp, Ioo01)),
        Sp, Parenthesized(body), Thin, F.Id("d"), X(variable));

    private static Formula FunctionDefinition() => All("α", All("σ",
        Equal(Typed(Local("fermionicRenyiFunction", Alpha, X("σ")), Reals),
            At(Qualified("D5", "S3", "Entropy", "RenyiCombining", "BinaryRenyiCombining", "hRenyi"),
                Alpha, Div(Add(D(1), X("σ")), D(2))))));
    private static Formula WeightDefinition()
    {
        Formula u = X("u");
        Formula angle = Mul(Qualified("Real", "pi"), Alpha);
        Formula gap = Sub(D(1), Pow(u, D(2)));
        Formula numerator = Mul(Mul(Mul(D(2), Alpha), At(Qualified("Real", "sin"), angle)),
            Pow(gap, Sub(Alpha, D(1))));
        Formula denominator = Mul(Mul(Qualified("Real", "pi"), Sub(D(1), Alpha)),
            Add(Add(Pow(Add(D(1), u), Mul(D(2), Alpha)), Pow(Sub(D(1), u), Mul(D(2), Alpha))),
                Mul(Mul(D(2), Pow(gap, Alpha)), At(Qualified("Real", "cos"), angle))));
        return All("α", All("u", Equal(Typed(Local("fermionicWeight", Alpha, u), Reals), Div(numerator, denominator))));
    }
    private static Formula WeightPositive() => All("α", All("u", OrderRange(
        Imp(LE(D(0), X("u")), Imp(LT(X("u"), D(1)), LT(D(0), Local("fermionicWeight", Alpha, X("u"))))))));
    private static Formula WeightIntegrable() => All("α", OrderRange(Integrable(Local("fermionicWeight", Alpha))));
    private static Formula Representation()
    {
        Formula integrand = Mul(Local("fermionicWeight", Alpha, X("u")),
            LogOf(Sub(D(1), Mul(Pow(X("u"), D(2)), Pow(X("σ"), D(2))))));
        return All("α", All("σ", OrderRange(Imp(LE(new Formula.Absolute(X("σ")), D(1)),
            And(Integrable(LambdaOf("u", integrand)),
                Equal(Local("fermionicRenyiFunction", Alpha, X("σ")),
                    Add(LogOf(D(2)), Integral("u", integrand))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fermionic Gaussian Renyi function has a positive logarithmic Stieltjes representation for every real order strictly between zero and one.",
        H("A positive logarithmic representation of fermionic Renyi entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fermionic-renyi-function"), DeclarationHandle.Create(Module + ".fermionicRenyiFunction"),
                H("The single-mode fermionic entropy"), StatementSource.FromAuthor(Disp(FunctionDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Evaluate the binary Renyi function hRenyi at the probability (1+σ)/2. For |σ|≤1 and positive order different from one, this is the logarithm of the sum of the two powers ((1+σ)/2)^α and ((1−σ)/2)^α, divided by 1−α. It is the single-mode function in Eq. renyi_fermionic_1 of Camilo, Landi and Eliëns (RenyiGaussian_v2.tex, lines 297–301). The total real-valued definition uses Real.rpow and Real.log; it does not insert the Shannon limit at order one."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fermionic-weight"), DeclarationHandle.Create(Module + ".fermionicWeight"),
                H("The logarithmic density"), StatementSource.FromAuthor(Disp(WeightDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The density has the positive sine factor for orders between zero and one, a power of 1−u², and a denominator with a plus cosine term. The formula defines a total real function; the positivity and integrability assertions below specify its entropy range."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weight-positive"), DeclarationHandle.Create(Module + ".weight_pos"),
                H("Strict positivity of the density"), StatementSource.FromAuthor(Disp(WeightPositive())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For 0<α<1 and 0≤u<1, the sine and the power of 1−u² are positive. Rescaling the denominator gives a positive multiple of the Poisson quadratic at a negative real argument. All numerator and denominator factors therefore have the signs needed for strict positivity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weight-integrable"), DeclarationHandle.Create(Module + ".weight_integrable"),
                H("Integrability on the open unit interval"), StatementSource.FromAuthor(Disp(WeightIntegrable())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Multiply the bosonic density of order β by β−1. The fermionic density is the difference of these scaled densities at orders 2α and α, divided by 1−α. Each scaled density is integrable for 0<β<2; at β=1 it is identically zero. The difference formula proves integrability even when 2α=1."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stieltjes-representation"), DeclarationHandle.Create(Module + ".stieltjes_representation"),
                H("The positive logarithmic representation"), StatementSource.FromAuthor(Disp(Representation())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive spectral argument at most one, apply the bosonic logarithmic representation to its reciprocal at orders α and 2α. Scaling each identity by its order minus one removes the exceptional order one, where the identity reduces directly to elementary logarithms. Factoring the difference of squares into the difference and sum of powers and subtracting the two logarithmic identities gives the fermionic formula with constant log 2. The same density difference gives integrability of the logarithmic integrand, including the pure-mode endpoint. At spectral argument zero the integrand vanishes and h_half evaluates the entropy as log 2. Evenness of the entropy and the squared spectral argument then gives the formula for negative arguments, including minus one."))), DescribeRole.Theorem))));
}
