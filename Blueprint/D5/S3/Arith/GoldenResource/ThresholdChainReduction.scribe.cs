using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ThresholdChainReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ThresholdChainReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic Robin margin on a finite prime exponent box is minimized on "
            + "the chain ordered by exact marginal benefit per logarithmic unit.",
        H("Exact Exponent Box Chain Reduction"),
        Blocks(
            Entry("exponentLayers", "threshold-chain-added-layers", "Added layers",
                LayersFormula(), DescribeRole.Definition,
                "For divisibility endpoints B and U, each layer records its prime and its "
                    + "exponent index. The lower endpoint's exponent is excluded and the "
                    + "upper endpoint's exponent is included."),
            Entry("exponentBox", "threshold-chain-exponent-box", "Exponent box",
                BoxFormula(), DescribeRole.Definition,
                "The divisors of U that are multiples of B have precisely the prime "
                    + "exponents between the two endpoints. When B divides the positive U, "
                    + "this set contains B."),
            Entry("layerChain", "threshold-chain-integer-chain", "Ordered integer chain",
                ChainFormula(), DescribeRole.Definition,
                "An equivalence e enumerates every added layer exactly once. Its first j "
                    + "entries multiply B by their prime factors, including repeated primes "
                    + "at different layers. The empty product gives B."),
            Entry("threshold_chain_reduction", "robin-margin-exact-chain-reduction",
                "The chain attains the box minimum", ResultFormula(), DescribeRole.Theorem,
                "Assume B is at least three, U is nonzero, and B divides U. The enumeration "
                    + "orders the real goldenLayerMarginal values in descending order; "
                    + "equal values may occur in either order. Write M for the number of added layers. "
                    + "There are M+1 chain positions. The displayed cardinalities count the "
                    + "full box and all added layers, including zero-width prime directions. "
                    + "Every chain prefix lies in the box and includes every lower "
                    + "available layer of any prime that it includes. One chain position "
                    + "attains the minimum both over the box and over the chain.",
                "At a box minimizer, the strictly concave function x mapped to log(log x) on x>1 "
                    + "has a supporting tangent with positive slope. A permitted increase "
                    + "of one prime exponent has marginal strictly below that slope; "
                    + "a permitted decrease has marginal strictly above it. Decreasing "
                    + "prime-layer marginals identify the adopted layers as one complete "
                    + "threshold prefix. Their prime product reconstructs the minimizing "
                    + "integer. All comparisons use real logarithms; an approximation "
                    + "does not supply the required order inequalities."))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title,
        Formula formula, DescribeRole role, params string[] paragraphs) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks([.. paragraphs.Select(text => Paragraph(Text(text)))]), role);

    private static Formula LayersFormula()
    {
        Formula b = F.Id("B"), u = F.Id("U"), p = F.Id("p"), k = F.Id("k");
        return Disp(Equal(Layers(b, u), SetBuilder(Seq(Open, p, Comma, k, Close),
            And(In(p, Primes(u)), And(Lt(V(b, p), k), Le(k, V(u, p)))))));
    }

    private static Formula BoxFormula()
    {
        Formula b = F.Id("B"), u = F.Id("U"), n = F.Id("n");
        return Disp(Equal(Box(b, u), SetBuilder(n,
            And(In(n, Call("divisors", u)), Divides(b, n)))));
    }

    private static Formula ChainFormula()
    {
        Formula b = F.Id("B"), u = F.Id("U"), e = F.Id("e"), j = F.Id("j"), i = F.Id("i");
        Formula product = Seq(Prod, Underscore, Grp(Seq(i, Sp, F.Lt, Sp, M(b, u), Comma,
            Sp, i, Sp, F.Lt, Sp, j)), Sp, Call("fst", Call("e", i)));
        return Disp(Equal(Chain(b, u, e, j), Times(b, product)));
    }

    private static Formula ResultFormula()
    {
        Formula b = F.Id("B"), u = F.Id("U"), e = F.Id("e");
        Formula p = F.Id("p"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k"), r = F.Id("r");
        Formula m = M(b, u), c = Chain(b, u, e, j);
        Formula pi = Call("fst", Call("e", i)), ki = Call("snd", Call("e", i));
        Formula order = ForAll([Bound("i", Call("Fin", m)), Bound("r", Call("Fin", m))],
            Implies(Le(i, r), Le(Eta(Call("e", r)), Eta(Call("e", i)))));
        Formula hypothesis = And(Le(D(3), b), And(Seq(u, Sp, Neq, Sp, D(0)),
            And(Divides(b, u), order)));
        Formula layerCount = Equal(m, Indexed(Sum, p, Primes(u), MinusOf(V(u, p), V(b, p))));
        Formula boxCount = Equal(Call("card", Box(b, u)), Indexed(Prod, p, Primes(u),
            Plus(MinusOf(V(u, p), V(b, p)), D(1))));
        Formula legal = ForAll([Bound("j", Naturals())], Implies(Le(j, m), In(c, Box(b, u))));
        Formula closure = ForAll([Bound("j", Naturals()), Bound("i", Call("Fin", m)),
            Bound("k", Naturals())], Implies(And(Le(j, m), And(Lt(i, j),
                And(Lt(V(b, pi), k), Le(k, ki)))),
            Exists([Bound("r", Call("Fin", m))], And(Lt(r, j),
                Equal(Call("e", r), Seq(Open, pi, Comma, k, Close))))));
        Formula boxValues = Call("image", F.Id("robinLogMargin"), Box(b, u));
        Formula chainValues = SetBuilder(Margin(c), And(In(j, Naturals()), Le(j, m)));
        Formula least = Exists([Bound("j", Naturals())], And(Le(j, m),
            And(Call("IsLeast", boxValues, Margin(c)), Call("IsLeast", chainValues, Margin(c)))));
        Formula equality = Equal(Call("sInf", boxValues), Call("sInf", chainValues));
        return Disp(ForAll([Bound("B", Naturals()), Bound("U", Naturals()),
            Bound("e", Call("Equiv", Call("Fin", m), Layers(b, u)))], Implies(hypothesis,
            And(layerCount, And(boxCount, And(legal, And(closure, And(least, equality))))))));
    }

    private static Formula Layers(Formula b, Formula u) => Call("exponentLayers", b, u);
    private static Formula Box(Formula b, Formula u) => Call("exponentBox", b, u);
    private static Formula Chain(Formula b, Formula u, Formula e, Formula j) => Call("layerChain", b, u, e, j);
    private static Formula V(Formula n, Formula p) => Call("factorization", n, p);
    private static Formula M(Formula b, Formula u) => Call("card", Layers(b, u));
    private static Formula Primes(Formula u) => Call("primeFactors", u);
    private static Formula Margin(Formula n) => Call("robinLogMargin", n);
    private static Formula Eta(Formula pk) => Call("goldenLayerMarginal", Call("fst", pk), Call("snd", pk));
    private static Formula In(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula MinusOf(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula SetBuilder(Formula x, Formula condition) =>
        Seq(OpenBrace, x, Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Indexed(Formula symbol, Formula variable, Formula domain, Formula term) =>
        Seq(symbol, Underscore, Grp(In(variable, domain)), Sp, Open, term, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula domain) => new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Plus(Formula x, Formula y) => Seq(x, F.Plus, y);
    private static Formula Times(Formula x, Formula y) => Seq(x, F.Cdot, y);
}
