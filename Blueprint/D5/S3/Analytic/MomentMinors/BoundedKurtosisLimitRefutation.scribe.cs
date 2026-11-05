using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MomentMinors;

internal sealed class BoundedKurtosisLimitRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/StatisticalMechanics/meerweeks2024boundedmoments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-point probability law exceeds the proposed two-sided kurtosis upper limit.",
        H("A counterexample to the two-sided kurtosis limits"), Blocks(
            Describe.Lean(
                DescribeId.Create("kurtosis-bound"),
                DeclarationHandle.Create(Module + ".kurtosisBound"),
                H("The two-point kurtosis expression"),
                StatementSource.FromAuthor(Disp(KurtosisBoundFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For real δ and δm, kurtosisBound is (δ/δm − δm/δ)² + 1. "
                    + "This is the expression D₄,ₘ(δ) in Meer and Weeks, "
                    + "arXiv:2308.05006v2, plos_latex_template.tex, lines 451–456. "
                    + "The real-valued definition also includes zero arguments, using real "
                    + "division with inverse zero equal to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The proposed limits for bounded probability laws"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The proposition concerns every real interval with L < U and every "
                    + "probability measure μ concentrated almost everywhere on that interval, "
                    + "with positive mean and positive second central moment. Here mean μ "
                    + "is the integral of x, and centralMoment id k μ is the integral of "
                    + "(x − mean μ)ᵏ. The standard deviation σ is the square root of the second "
                    + "central moment, δ is σ divided by the mean, and D4 is the fourth central "
                    + "moment divided by the square of the second. These are the moment "
                    + "conventions of plos_latex_template.tex, lines 228–236 and 290–293. "
                    + "The quantities δmin and δmax are the absolute normalized distances "
                    + "from the mean to L and U; δ₁ and δ₂ are their minimum and maximum, "
                    + "and δ′ is the square root of their product, as in lines 437–460. "
                    + "When δ < δ₁, the proposition requires D4 to lie between 1 and "
                    + "kurtosisBound δ δ₂. When δ₁ ≤ δ and δ < δ′, it requires D4 to lie "
                    + "between kurtosisBound δ δ₁ and kurtosisBound δ δ₂. These are the "
                    + "two implications in equation D4mostgeneral, lines 461–464, read as "
                    + "bounds for all such probability laws in the sense suggested at line 467. "
                    + "The proposition makes no assertion for δ ≥ δ′."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A three-point counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let ν assign masses 1/4, 1/2 and 1/4 to the real points 1, 2 and 3. "
                        + "It is the sum of the corresponding weighted Dirac measures. "
                        + "The masses are nonnegative and sum to one, so ν is a probability "
                        + "measure. Each of the three points belongs to [1,3], giving "
                        + "1 ≤ x ≤ 3 almost everywhere.")),
                    Paragraph(Text(
                        "For every function f from the reals to the reals, f is integrable "
                        + "against each of these weighted Dirac measures. Splitting the "
                        + "integral over their sum therefore gives "
                        + "∫ f dν = f(1)/4 + f(2)/2 + f(3)/4. Taking f(x) = x yields "
                        + "mean ν = 1/4 + 2/2 + 3/4 = 2. Subtracting this mean and taking "
                        + "the second power yields the second central moment "
                        + "1/4 + 0 + 1/4 = 1/2. Taking the fourth power gives the same "
                        + "value 1/2 for the fourth central moment.")),
                    Paragraph(Text(
                        "Put s = √(1/2). Since 1/2 < 1, the square-root inequality gives "
                        + "s < 1, hence s/2 < 1/2. Also s² = 1/2 and "
                        + "(1/2)/(s/2) = 2s, while (s/2)/(1/2) = s. Substitution into "
                        + "the two-point expression gives "
                        + "kurtosisBound (s/2) (1/2) = (s − 2s)² + 1 = 3/2.")),
                    Paragraph(Text(
                        "Suppose claim holds. Apply it with L = 1, U = 3 and μ = ν. "
                        + "The mean and variance are positive, and the interval condition "
                        + "was established above. Substituting the computed moments gives "
                        + "δ = s/2, δmin = |1 − 1/2| = 1/2 and "
                        + "δmax = |1 − 3/2| = 1/2. Thus δ₁ = δ₂ = 1/2 and "
                        + "D4 = (1/2)/(1/2)² = 2. Since δ < δ₁, the upper inequality "
                        + "in the first implication gives 2 ≤ kurtosisBound (s/2) (1/2). "
                        + "The value 3/2 computed above would then give 2 ≤ 3/2, "
                        + "a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("meer-weeks-2024-bounded-kurtosis-limit-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula KurtosisBoundFormula() => All("δ", Reals(), All("δm", Reals(),
        Equal(Typed(At(Local("kurtosisBound"), X("δ"), X("δm")), Reals()),
            Add(Power(Subtract(Divide(X("δ"), X("δm")), Divide(X("δm"), X("δ"))), 2),
                Typed(D(1), Reals())))));

    private static Formula ClaimFormula()
    {
        Formula upper = LessOrEqual(X("D4"), At(Local("kurtosisBound"), X("δ"), X("δ₂")));
        Formula first = Arrow(Less(X("δ"), X("δ₁")),
            Conjunction(LessOrEqual(Typed(D(1), Reals()), X("D4")), upper));
        Formula second = Arrow(LessOrEqual(X("δ₁"), X("δ")), Arrow(Less(X("δ"), X("δ'")),
            Conjunction(LessOrEqual(At(Local("kurtosisBound"), X("δ"), X("δ₁")), X("D4")), upper)));
        Formula body = Let("D4", Divide(Moment(4), Power(Moment(2), 2)), Conjunction(first, second));
        body = Let("δ'", At(Qualified("Real", "sqrt"), Multiply(X("δ₁"), X("δ₂"))), body);
        body = Let("δ₂", At(Qualified("max"), X("δmin"), X("δmax")), body);
        body = Let("δ₁", At(Qualified("min"), X("δmin"), X("δmax")), body);
        body = Let("δmax", new Formula.Absolute(Subtract(Typed(D(1), Reals()), Divide(X("U"), Mean()))), body);
        body = Let("δmin", new Formula.Absolute(Subtract(Typed(D(1), Reals()), Divide(X("L"), Mean()))), body);
        body = Let("δ", Divide(X("σ"), Mean()), body);
        body = Let("σ", At(Qualified("Real", "sqrt"), Moment(2)), body);
        Formula support = At(Qualified("Filter", "Eventually"),
            LambdaOf("x", Reals(), Conjunction(LessOrEqual(X("L"), X("x")), LessOrEqual(X("x"), X("U")))),
            At(Qualified("MeasureTheory", "ae"), Mu));
        return All("L", Reals(), All("U", Reals(), Arrow(Less(X("L"), X("U")),
            All("μ", At(Qualified("MeasureTheory", "Measure"), Reals()),
                Arrow(At(Qualified("MeasureTheory", "IsProbabilityMeasure"), Mu),
                    Arrow(support, Arrow(Less(Typed(D(0), Reals()), Mean()),
                        Arrow(Less(Typed(D(0), Reals()), Moment(2)), body))))))));
    }

    private static Formula Moment(byte k) => At(Qualified("ProbabilityTheory", "centralMoment"),
        Qualified("id"), Typed(D(k), Naturals()), Mu);
    private static Formula Mean() =>
        At(Qualified("D5", "S3", "Analytic", "MomentMinors", "Defs", "mean"), Mu);
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Analytic", "MomentMinors", "BoundedKurtosisLimitRefutation", name);
    private static Formula X(string name) => name switch
    {
        "μ" => Mu,
        "σ" => SigmaLower,
        "δ" => DeltaLower,
        "δm" => Seq(DeltaLower, Grp(F.Id("m"))),
        "δmin" => Seq(DeltaLower, Grp(F.Id("min"))),
        "δmax" => Seq(DeltaLower, Grp(F.Id("max"))),
        "δ₁" => new Formula.Subscript(DeltaLower, D(1)),
        "δ₂" => new Formula.Subscript(DeltaLower, D(2)),
        "δ'" => Seq(DeltaLower, Apos),
        _ => F.Id(name)
    };
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(X(name), Reals()), Sp, Colon, Eq, Sp, value, Semi, Sp, Parenthesized(body));
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, byte exponent) =>
        new Formula.Power(Parenthesized(value), Typed(D(exponent), Naturals()));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
