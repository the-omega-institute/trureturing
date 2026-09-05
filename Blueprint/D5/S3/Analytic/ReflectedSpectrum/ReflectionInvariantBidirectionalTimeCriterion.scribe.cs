using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class ReflectionInvariantBidirectionalTimeCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/"
            + "ReflectionInvariantBidirectionalTimeCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflected two-branch Gramian is finite at every proper discount exactly "
            + "at zero transverse displacement.",
        H("Reflection-Invariant Bidirectional Time Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bidirectional-gramian-term-definition"),
                DeclarationHandle.Create(Prefix + "bidirectionalGramianTerm"),
                H("The complete future-past Gramian term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The term is the sum of the two geometric powers obtained from both "
                        + "coordinates of the frozen reflected pair after a doubled observation "
                        + "period. It carries the future and past branches without selecting an "
                        + "orientation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bidirectional-convergence-radius-definition"),
                DeclarationHandle.Create(Prefix + "bidirectionalConvergenceRadius"),
                H("The first bidirectional singular radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The radius is exp(-2 P |delta|), the smaller of the reciprocal branch "
                        + "radii. It is invariant under changing the sign of delta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bidirectional-geometric-summability"),
                DeclarationHandle.Create(Prefix + "bidirectional_gramian_summable_iff"),
                H("Both geometric ratios control bidirectional summability"),
                StatementSource.FromAuthor(SummabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonnegative discount, comparison with the nonnegative combined "
                        + "series recovers summability of each branch. The pinned geometric-series "
                        + "criterion then identifies the two strict ratio bounds, and their sum "
                        + "proves the converse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflection-invariant-bidirectional-time-criterion"),
                DeclarationHandle.Create(Prefix
                    + "reflection_invariant_bidirectional_time_criterion"),
                H("Zero displacement is exactly complete discounted finiteness"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a positive observation period, zero displacement is equivalent to "
                            + "summability of the complete future-past series for every discount "
                            + "between zero and one.")),
                    Paragraph(Text(
                        "Changing the sign of delta exchanges the two summands and leaves their "
                            + "sum fixed. The common first radius still recovers |delta| exactly; "
                            + "a nonzero displacement is equivalent to that radius being below "
                            + "one."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare")),
        ]));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Term(
        Formula delta, Formula period, Formula beta, Formula n) =>
        Call("bidirectionalGramianTerm", delta, period, beta, n);

    private static Formula Radius(Formula delta, Formula period) =>
        Call("bidirectionalConvergenceRadius", delta, period);

    private static Formula SummabilityFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula delta = F.Id("delta");
        Formula period = F.Id("P");
        Formula beta = new Formula.Symbol(FormulaIdentifier.Create("beta"));
        Formula n = F.Id("n");
        Formula doubledPeriod = Multiply(D(2), period);
        Formula pair = Call("reflectedGrowthPair", delta, doubledPeriod);
        Formula firstRatio = Multiply(beta, Call("fst", pair));
        Formula secondRatio = Multiply(beta, Call("snd", pair));
        Formula summable = Call("Summable", Lambda(n, Term(delta, period, beta, n)));
        Formula ratioBounds = And(
            LessThan(new Formula.Norm(firstRatio), D(1)),
            LessThan(new Formula.Norm(secondRatio), D(1)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("delta", reals),
                Bound("P", reals),
                Bound("beta", reals),
            ],
            ImpliesFormula(LessOrEqual(D(0), beta), IffFormula(summable, ratioBounds))));
    }

    private static Formula MainFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula delta = F.Id("delta");
        Formula period = F.Id("P");
        Formula beta = new Formula.Symbol(FormulaIdentifier.Create("beta"));
        Formula n = F.Id("n");
        Formula zeroSplit = Equal(delta, D(0));
        Formula discountDomain = And(
            LessOrEqual(D(0), beta), LessThan(beta, D(1)));
        Formula allDiscounts = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("beta", reals)],
            ImpliesFormula(
                discountDomain,
                Call("Summable", Lambda(n, Term(delta, period, beta, n)))));
        Formula criterion = IffFormula(zeroSplit, allDiscounts);
        Formula reflectionInvariant = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("beta", reals), Bound("n", naturals)],
            Equal(
                Term(new Formula.Negate(delta), period, beta, n),
                Term(delta, period, beta, n)));
        Formula radius = Radius(delta, period);
        Formula recoveryCoefficient = new Formula.Negate(
            new Formula.Fraction(D(1), Multiply(D(2), period)));
        Formula recovery = Equal(
            new Formula.Absolute(delta),
            Multiply(recoveryCoefficient, Call("log", radius)));
        Formula radiusDefect = IffFormula(
            new Formula.Not(zeroSplit), LessThan(radius, D(1)));
        Formula conclusion = And(
            criterion,
            And(reflectionInvariant, And(recovery, radiusDefect)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("delta", reals), Bound("P", reals)],
            ImpliesFormula(LessThan(D(0), period), conclusion)));
    }
}
