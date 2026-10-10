using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ActualOptimizerPrimeLossDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ActualOptimizerPrimeLoss.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual arbitrary-optimizer weighted prime loss",
        H("Actual pressure defect and directed prime bands"),
        Blocks(
            Paragraph(Text(
                "The pressure is the attained supremum of the original unrestricted "
                + "goldenResourceObjective. The defect is actualPressure(price x) minus "
                + "goldenResourceObjective(price x,n), with n an arbitrary positive optimizer "
                + "at the original price price b. No largest optimizer, clock, curvature, or "
                + "tie exclusion is used.")),
            Paragraph(Text(
                "The forward band is the finite set of primes b < p <= x-1 and the reverse "
                + "band is the finite set x < p <= b-1. The one-unit endpoints are retained. "
                + "The first-layer log inequalities force absence in the forward band and "
                + "adoption in the reverse band for every original optimizer, including all "
                + "equality choices outside these strict bands.")),
            Describe.Lean(
                DescribeId.Create("actual-forward-band-selection"),
                DeclarationHandle.Create(Prefix + "forward_band_selection"),
                H("Every forward-band prime is absent at the original optimizer"),
                StatementSource.FromAuthor(ForwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof uses the weak global threshold criterion and the strict "
                    + "successor-log bounds for the first layer. It does not choose a minimal "
                    + "optimizer or silently resolve an original-price tie."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-reverse-band-selection"),
                DeclarationHandle.Create(Prefix + "reverse_band_selection"),
                H("Every reverse-band prime is adopted at the original optimizer"),
                StatementSource.FromAuthor(ReverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reverse endpoint p <= b-1 is inclusive in the integer prime set, "
                    + "while the real price comparison remains strict at the first layer. "
                    + "This keeps the reverse band valid at equality and at empty bands."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-pressure-defect-weighted-consumer"),
                DeclarationHandle.Create(Prefix + "actual_optimizer_defect_ge_of_theta_interval_lower"),
                H("Actual defect consumer for the directed weighted bands"),
                StatementSource.FromAuthor(ConsumerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This consumer keeps the actual pressure defect on the conclusion side. "
                    + "Its two weighted-band inequalities and their theta-to-integral charge "
                    + "are explicit premises while the finite step-integral and real theta "
                    + "supplier bridge remains unfinished. The supplied ordinary audit proves "
                    + "that bridge mathematically; this file does not claim that Lean acceptance "
                    + "until those premises are formalized."))),
                DescribeRole.Theorem))));

    private static Formula ForwardFormula()
    {
        Formula b = F.Id("b"), x = F.Id("x"), n = F.Id("n"), p = F.Id("p");
        return Disp(ForAll([Bound("b", Reals()), Bound("x", Reals()), Bound("n", Naturals()),
            Bound("p", Naturals())],
            Implies(And(Lt(One(), b), And(Lt(b, x), And(
                Call("IsGoldenResourceOptimal", Call("price", b), n),
                Call("forwardMember", p, b, x))),
                Eq(Call("factorization", n, p), Zero()))));
    }

    private static Formula ReverseFormula()
    {
        Formula x = F.Id("x"), b = F.Id("b"), n = F.Id("n"), p = F.Id("p");
        return Disp(ForAll([Bound("x", Reals()), Bound("b", Reals()), Bound("n", Naturals()),
            Bound("p", Naturals())],
            Implies(And(Lt(One(), x), And(Lt(x, b), And(
                Call("IsGoldenResourceOptimal", Call("price", b), n),
                Call("reverseMember", p, x, b))),
                Le(One(), Call("factorization", n, p)))));
    }

    private static Formula ConsumerFormula()
    {
        Formula x = F.Id("x"), b = F.Id("b"), n = F.Id("n"), X = F.Id("X"), e = F.Id("epsilon"), H0 = F.Id("H0");
        Formula charge = Call("thetaCharge", e, Add(H0, One()), X, x, b);
        return Disp(ForAll([Bound("X", Reals()), Bound("epsilon", Reals()), Bound("H0", Reals()),
            Bound("x", Reals()), Bound("b", Reals()), Bound("n", Naturals())],
            Implies(And(Call("priceBand", X, x, b), And(
                Call("IsGoldenResourceOptimal", Call("price", b), n), And(
                    Call("forwardWeightedMassBound", x, b, n), And(
                        Call("reverseWeightedMassBound", x, b, n),
                        Call("thetaChargeBound", X, e, H0, x, b)))),
                Le(charge, Call("actualDefect", x, b, n)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula One() => D(1);
    private static Formula Zero() => D(0);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
