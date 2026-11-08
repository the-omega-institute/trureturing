using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.BosonicRenyiStieltjes;

internal sealed class PoissonWeightDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight";
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
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Angle => Mul(Qualified("Real", "pi"), Alpha);
    private static Formula SinAngle => At(Qualified("Real", "sin"), Angle);
    private static Formula CosAngle => At(Qualified("Real", "cos"), Angle);
    private static Formula OrderRange(Formula body) => Imp(LT(D(0), Alpha),
        Imp(LT(Alpha, D(2)), Imp(NE(Alpha, D(1)), body)));
    private static Formula Integrable(Formula function, Formula domain) =>
        At(Qualified("MeasureTheory", "IntegrableOn"), function, domain, Qualified("MeasureTheory", "volume"));
    private static Formula Integral(string variable, Formula domain, Formula body) => Seq(
        new Formula.Subscript(Int, Seq(Typed(X(variable), Reals()), Sp, InMacro, Sp, domain)),
        Sp, Parenthesized(body), Thin, F.Id("d"), X(variable));

    private static Formula Denominator(Formula r) => Add(Sub(D(1), Mul(Mul(D(2), r), CosAngle)), Pow(r, D(2)));
    private static Formula DenominatorPositive() => All("α", All("r", OrderRange(LT(D(0), Denominator(X("r"))))));
    private static Formula SinePositive() => All("α", OrderRange(LT(D(0), Div(Negate(SinAngle), Sub(Alpha, D(1))))));
    private static Formula CosineStrict() => All("α", OrderRange(LT(CosAngle, D(1))));
    private static Formula DensityDefinition()
    {
        Formula q = X("q");
        Formula numerator = Mul(Mul(Alpha, Pow(q, Sub(Alpha, D(1)))), Negate(SinAngle));
        Formula denominator = Mul(Mul(Qualified("Real", "pi"), Sub(Alpha, D(1))), Denominator(Pow(q, Alpha)));
        return All("α", All("q", Equal(Typed(Local("density", Alpha, q), Reals()), Div(numerator, denominator))));
    }
    private static Formula Inverse(Formula value) => At(Qualified("Inv", "inv"), value);
    private static Formula ReflectionHypotheses(Formula body) => Imp(NE(Alpha, D(1)), Imp(LT(CosAngle, D(1)), body));
    private static Formula Reflection() => All("α", All("q", Imp(LT(D(0), X("q")), ReflectionHypotheses(
        Equal(Div(Local("density", Alpha, Inverse(X("q"))), Pow(X("q"), D(2))), Local("density", Alpha, X("q")))))));
    private static Formula ResolventReflection()
    {
        Formula q = X("q");
        Formula r = X("r");
        Formula jacobian = new Formula.Absolute(Negate(Inverse(Pow(q, D(2)))));
        Formula resolvent = Div(Local("density", Alpha, Inverse(q)), Add(r, Inverse(q)));
        Formula scaled = Seq(Parenthesized(jacobian), Sp, Cdot, Sp, Parenthesized(resolvent));
        return All("α", All("r", All("q", Imp(LT(D(0), r), Imp(LT(D(0), q), ReflectionHypotheses(
            Equal(scaled, Div(Mul(Local("density", Alpha, q), q), Add(D(1), Mul(r, q))))))))));
    }
    private static Formula StieltjesIntegral()
    {
        Formula r = X("r");
        Formula domain = At(Qualified("Set", "Ioi"), Typed(D(0), Reals()));
        Formula integrand = Div(Local("density", Alpha, X("q")), Add(r, X("q")));
        Formula value = Sub(Div(D(1), Mul(Sub(Alpha, D(1)), Sub(D(1), r))),
            Div(Mul(Alpha, Pow(r, Sub(Alpha, D(1)))), Mul(Sub(Alpha, D(1)), Sub(D(1), Pow(r, Alpha)))));
        return All("α", All("r", OrderRange(Imp(LT(D(0), r), Imp(LT(r, D(1)),
            And(Integrable(LambdaOf("q", integrand), domain), Equal(Integral("q", domain, integrand), value)))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The power Poisson density has reciprocal reflection symmetry and an explicit positive-axis Stieltjes transform.",
        H("The power Poisson density and its Stieltjes transform"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("power-poisson-denominator-positive"), DeclarationHandle.Create(Module + ".power_poisson_denominator_pos"),
                H("Strict positivity of the power Poisson denominator"), StatementSource.FromAuthor(Disp(DenominatorPositive())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real r, the Poisson quadratic is strictly positive when 0<α<2 and α is different from one. Below one, sin(πα)>0; above one, reflecting the angle makes its sine positive without changing its cosine. The sum-of-squares identity for the Poisson denominator proves the assertion in both cases."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sine-factor-positive"), DeclarationHandle.Create(Module + ".sine_factor_pos"),
                H("The signed sine factor"), StatementSource.FromAuthor(Disp(SinePositive())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Below one, sin(πα) is positive and α−1 is negative. Above one, the sine is negative and α−1 is positive. Thus −sin(πα)/(α−1) is strictly positive throughout the stated range."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cosine-strict"), DeclarationHandle.Create(Module + ".cosine_lt_one"),
                H("A nondegenerate Poisson angle"), StatementSource.FromAuthor(Disp(CosineStrict())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Positivity of the signed sine factor implies that sin(πα) is nonzero. Equality in the universal bound cos(πα)≤1 would force that sine to vanish, so the bound is strict."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("density"), DeclarationHandle.Create(Module + ".density"),
                H("The power Poisson density"), StatementSource.FromAuthor(Disp(DensityDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The density is obtained from the Poisson quadratic by the substitution p=q^α. Its numerator includes the derivative factor α q^(α−1) and the signed angular factor. Real powers and division make this a total real function; positivity is used only with the stated restrictions on α and q."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("density-reflection"), DeclarationHandle.Create(Module + ".density_reflection"),
                H("Reciprocal reflection of the density"), StatementSource.FromAuthor(Disp(Reflection())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Replacing q by its reciprocal multiplies the density by q². Real-power inversion and the Poisson denominator identity prove this equality for positive q whenever α differs from one and cos(πα)<1."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("density-resolvent-reflection"), DeclarationHandle.Create(Module + ".density_resolvent_reflection"),
                H("Reciprocal reflection with a resolvent"), StatementSource.FromAuthor(Disp(ResolventReflection())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The absolute Jacobian of q↦q⁻¹ is |−(q²)⁻¹|. Combining it with the reciprocal density identity transforms the resolvent at q⁻¹ into density(α,q) q/(1+r q). Positivity of r and q keeps the denominators nonzero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stieltjes-integral"), DeclarationHandle.Create(Module + ".stieltjes_integral"),
                H("The explicit Stieltjes transform"), StatementSource.FromAuthor(Disp(StieltjesIntegral())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The transform is integrable at zero and infinity by power bounds and reciprocal reflection. Work on a logarithmic strip of height 2π, using the removable extension of the transform at one and the regularized kernel at log r. The regularized kernel has zero boundary integral on each rectangle. The two horizontal edges give the jump across the negative real axis, equal to the density times the Poisson normalization. With the vertical integrals taken with respect to the increasing imaginary coordinate, the left limit is zero and the right limit is (2π) • (−complexTransform α r). The real part of the left limit minus the right limit is therefore 2π times the real part of the transform. Substituting q=exp(x) then gives the stated positive-axis integral for 0<r<1."))), DescribeRole.Theorem))));
}
