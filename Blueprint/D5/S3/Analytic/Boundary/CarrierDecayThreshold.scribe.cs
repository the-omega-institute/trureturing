using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class CarrierDecayThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Boundary/CarrierDecayThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A power-log counting bound gives the strict and endpoint summability thresholds.",
        H("Carrier Decay Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("carrier-counting-function"),
                DeclarationHandle.Create(Prefix + "carrierCountingFunction"),
                H("The carrier counting function counts members below a cutoff"),
                StatementSource.FromAuthor(CountingDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a set A of natural numbers, the counting function at n is Mathlib's "
                        + "natural predicate count below n. This fixes the source's cumulative "
                        + "count on the exact set carrier rather than replacing it by supplied "
                        + "shell data."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("carrier-decay-threshold"),
                DeclarationHandle.Create(Prefix + "carrier_decay_threshold"),
                H("Power-log counting decay gives both convergence regimes"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be a set of natural numbers whose counting function is eventually "
                            + "bounded by C times n to the delta divided by log n to the beta. "
                            + "The series of n to the minus q over A is summable whenever q is "
                            + "strictly larger than delta. At q equal to delta it is summable "
                            + "when beta is strictly larger than one.")),
                    Paragraph(Text(
                        "The proof partitions A into exact base-two logarithmic fibers. Their "
                            + "cardinalities are bounded by the cumulative counting hypothesis, "
                            + "and every term in a positive-exponent shell is bounded using its "
                            + "lower dyadic endpoint. Above delta, logarithmic powers are absorbed "
                            + "by a smaller exponential gap and the shell bounds form a geometric "
                            + "series. At the endpoint the exponential factors cancel and leave "
                            + "a shifted p-series of exponent beta.")),
                    Paragraph(Text(
                        "The statement does not assume delta or C is positive. When a negative "
                            + "delta makes the displayed majorant tend to zero, the eventual "
                            + "integer count forces A to be finite. The same argument handles "
                            + "delta zero at the logarithmic endpoint, so no unstated positivity "
                            + "restriction is added.")),
                    Paragraph(Text(
                        "Repository, pinned-library, and Lean ecosystem searches found no exact "
                            + "owner. The proof directly applies the canonical natural count, "
                            + "exact summable partition, real p-series, logarithm-is-subpower, "
                            + "and geometric-series results. The indicator formulation is the "
                            + "series over the original set A; totalization at zero changes only "
                            + "one finite term."))),
                DescribeRole.Theorem))));

    private static Formula CountingDefinition()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula setOfNaturals = Call("Set", naturals);
        Formula set = F.Id("A");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula predicate = Lambda(k, Member(k, set));
        Formula body = Equal(
            Call("carrierCountingFunction", set, n),
            Call("NatCount", predicate, n));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("A", setOfNaturals), Bound("n", naturals)],
            body));
    }

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula setOfNaturals = Call("Set", naturals);
        Formula set = F.Id("A");
        Formula c = F.Id("C");
        Formula delta = F.Id("delta");
        Formula beta = new Formula.Symbol(FormulaIdentifier.Create("beta"));
        Formula q = F.Id("q");
        Formula n = F.Id("n");

        Formula numerator = new Formula.Binary(
            c,
            FormulaBinaryOperator.Multiply,
            new Formula.Power(n, delta));
        Formula denominator = new Formula.Power(Call("log", n), beta);
        Formula countBound = new Formula.Relation(
            Call("carrierCountingFunction", set, n),
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Fraction(numerator, denominator));
        Formula eventualBound = Call("EventuallyAtTop", Lambda(n, countBound));

        Formula seriesTerm = new Formula.Binary(
            Call("indicator", set, n),
            FormulaBinaryOperator.Multiply,
            new Formula.Power(n, new Formula.Negate(q)));
        Formula summable = Call("Summable", Lambda(n, seriesTerm));
        Formula strictClause = ImpliesFormula(
            new Formula.Relation(delta, FormulaRelationOperator.LessThan, q),
            summable);
        Formula endpointPremise = And(
            Equal(q, delta),
            new Formula.Relation(D(1), FormulaRelationOperator.LessThan, beta));
        Formula endpointClause = ImpliesFormula(endpointPremise, summable);
        Formula conclusion = And(strictClause, endpointClause);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("A", setOfNaturals),
                Bound("C", reals),
                Bound("delta", reals),
                Bound("beta", reals),
                Bound("q", reals),
            ],
            ImpliesFormula(eventualBound, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
