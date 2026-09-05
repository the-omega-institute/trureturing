using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class CarrierDecayThresholdDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/SeriesInequalities/CarrierDecayThreshold."
            + "carrier_decay_threshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dyadic counting bound with logarithmic decay implies the sharp power-series threshold.",
        H("Carrier-Decay Threshold"),
        Blocks(Describe.Lean(
            DescribeId.Create("carrier-decay-threshold"),
            DeclarationHandle.Create(Declaration),
            H("Dyadic carrier decay gives power-series summability"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A be a carrier of positive natural numbers. Its counting function "
                        + "N_A(X) is the number of carrier elements strictly below X. Assume "
                        + "that, from some dyadic scale onward, the displayed normalized count "
                        + "is bounded by a logarithmic power.")),
                Paragraph(Text(
                    "Partition A into the shells with base-two logarithm k. Every positive "
                        + "integer belongs to exactly one shell, the kth shell is finite, and "
                        + "each of its terms is at most 2 to the power -qk.")),
                Paragraph(Text(
                    "For q greater than delta, the shell sums are eventually dominated by a "
                        + "geometric series. At q equal to delta, they are dominated by the "
                        + "shifted p-series with exponent beta, which converges for beta > 1.")),
                Paragraph(Text(
                    "The source's sufficiently-large real-variable bound is stated here in "
                        + "its direct dyadic form; fixed factors from log 2 and the endpoint "
                        + "2^(k+1) are absorbed into C. The formal statement also excludes zero "
                        + "from A and requires C, delta, and beta to be nonnegative, preventing "
                        + "totalized negative powers or sign-degenerate bounds."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrierType = Seq(naturals, Sp, To, Sp, F.Id("Prop"));
        Formula carrier = F.Id("A");
        Formula constant = F.Id("C");
        Formula delta = DeltaLower;
        Formula beta = Beta;
        Formula q = F.Id("q");
        Formula kZero = F.Id("kzero");
        Formula k = F.Id("k");
        Formula n = F.Id("n");

        Formula kPlusOne = Add(k, D(1));
        Formula dyadicEndpoint = Pow(D(2), kPlusOne);
        Formula normalizedCount = Mul(
            Call("countBelow", carrier, dyadicEndpoint),
            Pow(Pow(D(2), Grp(Seq(Minus, delta))), k));
        Formula dyadicBound = LeqFormula(
            normalizedCount,
            new Formula.Fraction(constant, Pow(kPlusOne, beta)));
        Formula eventualBound = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("kzero", naturals)],
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("k", naturals)],
                Implies(LeqFormula(kZero, k), dyadicBound)));
        Formula threshold = Or(
            LtFormula(delta, q),
            And(EqFormula(q, delta), LtFormula(D(1), beta)));
        Formula premises = And(
            new Formula.Not(Apply(carrier, D(0))),
            And(
                LeqFormula(D(0), constant),
                And(
                    LeqFormula(D(0), delta),
                    And(LeqFormula(D(0), beta), And(eventualBound, threshold)))));
        Formula summand = Seq(
            Open, n, Colon, Sp, Call("carrierSubtype", carrier), Sp,
            Mapsto, Sp, Pow(n, Grp(Seq(Minus, q))), Close);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("A", carrierType),
                Bound("C", reals),
                Bound("delta", reals),
                Bound("beta", reals),
                Bound("q", reals),
            ],
            Implies(premises, Call("Summable", summand))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Pow(Formula @base, Formula exponent) =>
        new Formula.Power(@base, exponent);

    private static Formula EqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LtFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LeqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
