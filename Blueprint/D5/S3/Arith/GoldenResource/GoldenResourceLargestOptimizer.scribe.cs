using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenResourceLargestOptimizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenResourceLargestOptimizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual integer contains every nonnegative-gain prime layer and supplies its exact logarithmic clock.",
        H("Full Largest CA Optimizer"),
        Blocks(
            Describe.Lean(DescribeId.Create("full-ca-layer-set"),
                DeclarationHandle.Create(Prefix + "fullCALayers"), H("All inclusive layers"),
                StatementSource.FromAuthor(LayersFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive lambda the set contains precisely all pairs (p,k) with p prime, k at least one, and lambda at most the marginal. It is finite because it lies in the existing strict support at lambda/2. All equality-price layers at all primes remain present. At nonpositive prices the definition returns the empty set; no optimizer assertion is made there."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-ca-inclusive-count"),
                DeclarationHandle.Create(Prefix + "fullCALayerCount"), H("Inclusive exponent counts"),
                StatementSource.FromAuthor(CountFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exponent is the cardinality of the full layer fiber at p. Marginal strict decrease identifies that fiber with a positive initial interval. Nonprime fibers are empty."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-ca-integer-product"),
                DeclarationHandle.Create(Prefix + "largestCA"), H("The constructed integer"),
                StatementSource.FromAuthor(ProductFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply one factor p for each adopted pair (p,k). Repeated prime factors encode the exponent stack. Prime factorization of this literal finite product proves the inclusive counts; they are not assumed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-ca-largest-realization"),
                DeclarationHandle.Create(Prefix + "largest_ca_spec"), H("Largest optimizer on all positive integers"),
                StatementSource.FromAuthor(SpecFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive real price the product is positive, its factorization equals the inclusive counts, nonprime counts vanish, and prime layer membership is exactly lambda <= marginal. The existing boundary criterion proves optimality. The lower boundary of any positive optimizer puts every one of its adopted layers inside this product, so it divides C(lambda). This proves the actual largest integer optimizer, including simultaneous ties at different primes.")),
                    Paragraph(Text("Repo-prior-exposed: the existing minimal strict-count construction, threshold criterion, pressure formula, local thresholds, decay, prime cutoff and future maximum were inspected and reused. The new arithmetic proof constructs and identifies the inclusive product; no claim of literature originality is made."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-ca-exact-log-clock"),
                DeclarationHandle.Create(Prefix + "largest_ca_clock"), H("Exact full-layer clock increment"),
                StatementSource.FromAuthor(ClockFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For 0 < lambda2 < lambda1, C(lambda1) divides C(lambda2). The difference of their logarithms is exactly the sum of log p over all positive prime layers with lambda2 <= marginal < lambda1. The proof consumes the constructed integer's factorization and literal product, the support difference, and the finite logarithmic product identity. A tie at lambda1 is already in both states and contributes zero; a tie at lambda2 is adopted by the later state and contributes log p.")),
                    Paragraph(Text("The intended actual time interface is C_t = C(g(t)) and A(t) = log C_t, with g(t)=1/(t log t) and t>1. The price-domain formula gives the corresponding inclusive activation test without assuming event roots. No reusable inverse-event-root API was found in the searched arithmetic sources, so the event-root bridge remains open. Finite sample prices b_p, if used downstream, are price or time parameters and are not identified with log C. LS1-LS4 sampling estimates, joint root placement, signed Robin estimates and full RH are not proved by this integer clock."))),
                DescribeRole.Theorem))));

    private static Formula C(Formula l) => Call("largestCA", l);
    private static Formula Layers(Formula l) => Call("fullCALayers", l);
    private static Formula Count(Formula l, Formula p) => Call("fullCALayerCount", l, p);
    private static Formula Marginal(Formula p, Formula k) => Call("goldenLayerMarginal", p, k);
    private static Formula Fact(Formula l, Formula p) => Call("factorization", C(l), p);
    private static Formula LayersFormula()
    {
        Formula l = F.Id("lambda"), p = F.Id("p"), k = F.Id("k");
        Formula pair = Seq(Open, p, Comma, k, Close);
        Formula support = SetBuilder(pair, Seq(N(), Times, N()),
            And(Le(D(1), k), And(Call("Prime", p), Le(l, Marginal(p, k)))));
        return Disp(All([B("lambda", R())], Imp(Lt(D(0), l), Eq(Layers(l), support))));
    }
    private static Formula CountFormula() => Disp(All([B("lambda", R()), B("p", N())],
        Eq(Count(F.Id("lambda"), F.Id("p")), Call("card", SetBuilder(
            Seq(Open, F.Id("q"), Comma, F.Id("k"), Close), Layers(F.Id("lambda")), Eq(F.Id("q"), F.Id("p")))))));
    private static Formula ProductFormula() => Disp(All([B("lambda", R())], Eq(C(F.Id("lambda")),
        Seq(Prod, Underscore, Grp(Seq(Open, F.Id("p"), Comma, F.Id("k"), Close,
            InMacro, Layers(F.Id("lambda")))), Sp, F.Id("p")))));
    private static Formula SpecFormula()
    {
        Formula l = F.Id("lambda"), p = F.Id("p"), k = F.Id("k"), m = F.Id("m");
        Formula counts = All([B("p", N())], Eq(Fact(l, p), Count(l, p)));
        Formula nonprime = All([B("p", N())], Imp(Call("NotPrime", p), Eq(Count(l, p), D(0))));
        Formula membership = All([B("p", N()), B("k", N())], Imp(Call("Prime", p),
            new Formula.Logic(And(Le(D(1), k), Le(k, Fact(l, p))), FormulaLogicOperator.Iff,
                And(Le(D(1), k), Le(l, Marginal(p, k))))));
        Formula greatest = All([B("m", N())], Imp(And(Le(D(1), m), Call("IsGoldenResourceOptimal", l, m)),
            new Formula.Relation(m, FormulaRelationOperator.Divides, C(l))));
        return Disp(All([B("lambda", R())], Imp(Lt(D(0), l), And(Le(D(1), C(l)),
            And(counts, And(nonprime, And(membership, And(Call("IsGoldenResourceOptimal", l, C(l)), greatest))))))));
    }
    private static Formula ClockFormula()
    {
        Formula l1 = F.Id("lambda1"), l2 = F.Id("lambda2");
        Formula increment = new Formula.Binary(Call("log", C(l2)), FormulaBinaryOperator.Subtract, Call("log", C(l1)));
        Formula support = SetBuilder(Seq(Open, F.Id("p"), Comma, F.Id("k"), Close),
            Layers(l2), Lt(Marginal(F.Id("p"), F.Id("k")), l1));
        Formula sum = Seq(Sum, Underscore, Grp(Seq(Open, F.Id("p"), Comma, F.Id("k"),
            Close, InMacro, support)), Sp, Call("log", F.Id("p")));
        return Disp(All([B("lambda1", R()), B("lambda2", R())], Imp(And(Lt(D(0), l2), Lt(l2, l1)),
            And(new Formula.Relation(C(l1), FormulaRelationOperator.Divides, C(l2)), Eq(increment, sum)))));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula SetBuilder(Formula x, Formula domain, Formula predicate) =>
        Seq(OpenBrace, x, Colon, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula.BoundVariable B(string name, Formula domain) => new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] bs, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. bs], body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
}
