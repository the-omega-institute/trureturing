using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class PrimeObserverCasimirCompleteMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Adelic/PrimeObserverCasimirCompleteMonotonicity."
            + "prime_observer_casimir_complete_monotonicity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The split-prime zero-minus-first regulator mode is completely monotone.",
        H("Prime Observer Casimir Complete Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-observer-casimir-complete-monotonicity"),
            DeclarationHandle.Create(Declaration),
            H("Alternating derivatives of the split-prime observer Casimir"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Golden split primes are the nonramified rational primes whose images "
                        + "are not prime in the golden integers. The phase function supplies "
                        + "their regulator angles.")),
                Paragraph(Text(
                    "Each Fourier mode is constructed as a prime-power Dirichlet "
                        + "coefficient. The Casimir is the logarithmic zero-mode reading "
                        + "minus the first-mode reading.")),
                Paragraph(Text(
                    "The prime-power coefficient is a nonnegative squared phase distance. "
                        + "Termwise logarithmic differentiation and prime-power support "
                        + "reindexing give the displayed signed double series throughout the "
                        + "half-plane sigma greater than one. The index k + 1 records the "
                        + "source's positive prime-power exponent."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat");
        Formula real = Call("Real");
        Formula phase = F.Id("phase");
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula sigma = F.Id("sigma");
        Formula casimir = Call("goldenObserverCasimir", phase);
        Formula phaseAtP = Apply(phase, p);
        Formula sign = Call("pow", Seq(Open, Minus, D(1), Close), m);
        Formula signedDerivative = Seq(
            sign, Sp, Times, Sp, Call("iteratedDeriv", m, casimir, sigma));
        Formula positiveExponent = Seq(Open, k, Sp, Plus, Sp, D(1), Close);
        Formula splitResidue = new Formula.Logic(
            EqualTo(Call("mod", p, D(5)), D(1)),
            FormulaLogicOperator.Or,
            EqualTo(Call("mod", p, D(5)), D(4)));
        Formula phaseDistance = Seq(
            D(1), Sp, Minus, Sp,
            Call("cos", Seq(positiveExponent, Sp, Times, Sp, phaseAtP)));
        Formula coefficientWeight = new Formula.Fraction(
            Seq(D(2), Sp, Times, Sp, Open, phaseDistance, Close),
            positiveExponent);
        Formula logarithmicWeight = new Formula.Power(
            Seq(Open, positiveExponent, Sp, Times, Sp, Call("log", p), Close),
            m);
        Formula decayWeight = new Formula.Power(
            p,
            Grp(Seq(Minus, Open, positiveExponent, Sp, Times, Sp, sigma, Close)));
        Formula splitSummand = Seq(
            coefficientWeight, Sp, Times, Sp,
            logarithmicWeight, Sp, Times, Sp, decayWeight);
        Formula summand = Seq(
            Begin, Grp(F.Id("cases")),
            splitSummand, Comma, Amp, splitResidue, RowBreak,
            D(0), Comma, Amp, F.Text, Grp(F.Id("otherwise")),
            End, Grp(F.Id("cases")));
        Formula differentiatedSeries = Seq(
            Sum, Underscore,
            Grp(p, Sp, InMacro, Sp, F.Id("NatPrimes")), Sp,
            Sum, Underscore,
            Grp(k, Sp, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N")))), Sp,
            summand);
        Formula derivativeClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("m", natural), Bound("sigma", real)],
            Implies(
                LessThan(D(1), sigma),
                EqualTo(signedDerivative, differentiatedSeries)));
        Formula termwiseNonnegativeClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("m", natural), Bound("sigma", real), Bound("p", Call("NatPrimes")),
                Bound("k", natural)],
            Implies(
                LessThan(D(1), sigma),
                new Formula.Relation(
                    D(0), FormulaRelationOperator.LessThanOrEqual, summand)));
        Formula nonnegativeClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("m", natural), Bound("sigma", real)],
            Implies(
                LessThan(D(1), sigma),
                new Formula.Relation(
                    D(0), FormulaRelationOperator.LessThanOrEqual, signedDerivative)));
        Formula conclusions = And(
            derivativeClause,
            And(termwiseNonnegativeClause, nonnegativeClause));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("phase", new Formula.TypeArrow(natural, real))],
            conclusions));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
