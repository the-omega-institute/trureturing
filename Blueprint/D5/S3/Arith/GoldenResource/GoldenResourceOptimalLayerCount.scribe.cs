using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenResourceOptimalLayerCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenResourceOptimalLayerCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a positive price, strictly profitable layer counts are the prime exponents of "
            + "a positive optimizer that divides every positive optimizer.",
        H("Golden Resource Optimal Layer Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-positive-layer-pair-finiteness"),
                DeclarationHandle.Create(Prefix + "positive_part_sum_finite_support"),
                H("The active prime-layer set is finite"),
                StatementSource.FromAuthor(FinitenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive lambda, all pairs consisting of a prime and a positive "
                        + "exponent with marginal strictly above lambda form a finite set. "
                        + "The frozen attainment theorem supplies an optimizer. Its boundary "
                        + "threshold bounds each active exponent, embedding all active pairs "
                        + "in a finite union of factorization intervals. This finite set "
                        + "supplies the support of the integer constructed below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-optimal-layer-count-definition"),
                DeclarationHandle.Create(Prefix + "optimalLayerCount"),
                H("Count of strictly profitable layers"),
                StatementSource.FromAuthor(CountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The count is the natural cardinality of the positive layers above the "
                        + "price, with primality included in the predicate. Nonprime directions "
                        + "therefore have count zero. The definition accepts every real price; "
                        + "the following specifications require a strictly positive price."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-positive-layer-count-interval"),
                DeclarationHandle.Create(Prefix + "positive_layers_eq_count_interval"),
                H("Active layers form the counted initial interval"),
                StatementSource.FromAuthor(IntervalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime and positive price, strict marginal decrease makes the "
                        + "finite active fiber downward closed among positive exponents. "
                        + "Taking its maximum and counting the resulting interval shows that "
                        + "the fiber is exactly the interval from one through its count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-minimal-exponent-count-optimizer"),
                DeclarationHandle.Create(Prefix + "optimal_layer_count_spec"),
                H("A simultaneous optimizer with minimal prime exponents"),
                StatementSource.FromAuthor(SpecFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive lambda there is a positive integer n whose "
                            + "factorization at every natural p equals the strict-gain layer "
                            + "count. It maximizes the resource objective and divides every "
                            + "positive optimizer, so each prime exponent is minimal.")),
                    Paragraph(Text(
                        "The finite pair set projects to a finite prime support. The product "
                            + "of these prime powers realizes all counts simultaneously. The "
                            + "count interval gives the next-layer upper threshold and the "
                            + "strict last-layer lower threshold; the frozen global criterion "
                            + "then proves optimality. Every other optimizer must contain all "
                            + "strictly profitable layers, yielding divisibility.")),
                    Paragraph(Text(
                        "Equality-price layers are excluded from this minimal configuration. "
                            + "This statement allows other optimizers at critical prices. The "
                            + "positive-part formula for the optimal value, a full description "
                            + "of equality-price choices, and the 5040 boundary are outside "
                            + "this slice."))),
                DescribeRole.Theorem))));

    private static Formula Active(Formula lambda, Formula p, Formula k) =>
        And(Le(D(1), k), And(Call("Prime", p), Lt(lambda, Marginal(p, k))));

    private static Formula Layers(Formula lambda, Formula p) =>
        SetBuilder(F.Id("k"), Naturals(), Active(lambda, p, F.Id("k")));

    private static Formula FinitenessFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula pair = Seq(Open, F.Id("p"), Comma, F.Id("k"), Close);
        Formula pairs = SetBuilder(pair, Seq(Naturals(), Times, Naturals()),
            Active(lambda, F.Id("p"), F.Id("k")));
        return Disp(ForAll([Bound("lambda", Reals())],
            Implies(Lt(D(0), lambda), Call("Finite", pairs))));
    }

    private static Formula CountFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula p = F.Id("p");
        return Disp(ForAll([Bound("lambda", Reals()), Bound("p", Naturals())],
            Equal(Call("optimalLayerCount", lambda, p), Call("ncard", Layers(lambda, p)))));
    }

    private static Formula IntervalFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula p = F.Id("p");
        return Disp(ForAll([Bound("lambda", Reals()), Bound("p", Naturals())],
            Implies(And(Lt(D(0), lambda), Call("Prime", p)),
                Equal(Layers(lambda, p),
                    Call("Icc", D(1), Call("optimalLayerCount", lambda, p))))));
    }

    private static Formula SpecFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula m = F.Id("m");
        Formula counts = ForAll([Bound("p", Naturals())],
            Equal(Call("factorization", n, p), Call("optimalLayerCount", lambda, p)));
        Formula minimal = ForAll([Bound("m", Naturals())],
            Implies(And(Le(D(1), m), Call("IsGoldenResourceOptimal", lambda, m)),
                new Formula.Relation(n, FormulaRelationOperator.Divides, m)));
        Formula witness = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("n", Naturals())], And(Le(D(1), n),
                And(counts, And(Call("IsGoldenResourceOptimal", lambda, n), minimal))));
        return Disp(ForAll([Bound("lambda", Reals())], Implies(Lt(D(0), lambda), witness)));
    }

    private static Formula SetBuilder(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Colon, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Marginal(Formula p, Formula k) => Call("goldenLayerMarginal", p, k);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
