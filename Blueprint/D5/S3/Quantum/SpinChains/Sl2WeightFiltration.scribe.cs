using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class Sl2WeightFiltrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral sl₂ weights give sharp rank bounds for endomorphisms lowering the weight filtration.",
        H("Weight filtration and maximal power ranks"),
        Blocks(
            Paragraph(Text("Let K be a field of characteristic zero and V a finite-dimensional K-vector space. The relations ef − fe = h, he − eh = 2e and hf − fh = −2f include the zero action. The space weightSpace(h,s) is the eigenspace of h at the scalar obtained from the integer s. IntegralWeights(h) means that a finite collection of integer weight spaces spans V. The spaces weightLE(h,s) and weightGE(h,s) are the sums of weights at most s and at least s, respectively. An inner iSup over a proposition is the indicated subspace when that proposition holds, and the zero subspace otherwise. Operator powers use composition; finrank denotes dimension over K.")),
            DefinitionNode("Sl2Relations", "The sl₂ commutator relations", RelationsDefinition()),
            DefinitionNode("weightSpace", "The integer weight space", WeightSpaceDefinition()),
            DefinitionNode("IntegralWeights", "Finite integral weight support", IntegralWeightsDefinition()),
            DefinitionNode("weightLE", "The lower weight filtration", WeightFiltrationDefinition(false)),
            DefinitionNode("weightGE", "The upper weight filtration", WeightFiltrationDefinition(true)),
            DefinitionNode("loweringMap", "The shifted lowering map", PowerMapDefinition(false)),
            DefinitionNode("raisingMap", "The shifted raising map", PowerMapDefinition(true)),
            Node("raising_pow_weight", "Raising shifts weights", Shift(true),
                "The commutator of h with e implies that the rth raising power increases weight by twice r."),
            Node("lowering_pow_weight", "Lowering shifts weights", Shift(false),
                "The commutator of h with f implies that the rth lowering power decreases weight by twice r."),
            Node("raising_locally_nilpotent", "Local raising nilpotence", Nilpotent(true),
                "Nonzero successive raising iterates have distinct eigenvalues. An infinite sequence of such vectors would be linearly independent, contradicting finite dimensionality."),
            Node("lowering_locally_nilpotent", "Local lowering nilpotence", Nilpotent(false),
                "Successive lowering iterates likewise have distinct weights, so every weight vector is eventually annihilated."),
            Node("lowering_pow_injective", "Injectivity above the exponent", Injective(true),
                "A lowering power is injective on weights at least its exponent. Local raising nilpotence supplies the kernel criterion, including the zero representation."),
            Node("raising_pow_injective", "Injectivity below the negative exponent", Injective(false),
                "Interchanging e and f and replacing h by its negative gives injectivity of raising powers on sufficiently negative weights."),
            Node("weight_finrank_symm", "Symmetry of weight dimensions", Symmetry(),
                "Injections in both directions between opposite weight spaces force their dimensions to agree."),
            Node("lowering_pow_surjective", "Surjectivity onto negative weights", Surjective(),
                "Lowering from the opposite positive weight is bijective. Factoring this power gives a preimage for every smaller lowering power with sufficiently negative target."),
            Node("lowering_rank_formula", "Exact rank of a lowering power", RankFormula(),
                "Split the representation at weight r. The lowering power is injective on the upper part and maps the lower part onto weights at most minus r minus one. The two image subspaces are disjoint."),
            Node("filtration_pow_map_le", "Iterated filtration decrease", FiltrationPower(),
                "Induction on the exponent adds the two-unit filtration decrease at each application. No exhaustiveness or boundedness assumption on the filtration is required."),
            Node("rank_comparison", "Maximal power ranks", Comparison(),
                "Restrict a power of T from weights at most r minus one to weights at most minus r minus one. Rank-nullity bounds its kernel from below. The exact lowering rank formula then gives the power-rank comparison for every natural exponent."),
            Node("eigenspace_rank_comparison", "Power ranks on commuting eigenspaces", EigenspaceComparison(),
                "For a scalar m, write W for eigenspace(U,m) and restrict(A,W) for the endomorphism induced by A on W. Commutation with U makes h, e, f and T preserve W, and the restricted operators satisfy the same sl₂ relations. Decompose a vector of W into its integer weight components. The differences between U applied to each component and m times that component lie in independent weight spaces and sum to zero, so each difference vanishes. Every selected sum of weight spaces therefore restricts to its intersection with W. In particular, the finite integral weight decomposition and the lower weight filtration restrict to W. The restricted T lowers this filtration by two, and the maximal power-rank comparison applies on W. This holds for every scalar m, including when W is zero, without assuming diagonalizability of U.")),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("sl-two-filtration-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/Sl2WeightFiltration." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock.Describe DefinitionNode(string name, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create("sl-two-filtration-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/Sl2WeightFiltration." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This declaration records the indicated sl₂ object and its defining expression."))),
            DescribeRole.Definition);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula fn, Formula arg) => new Formula.Apply(fn, [arg]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Member(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Assumption(Formula x, Formula body) => Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Ints));
    private static Formula End => Call("End", F.Id("K"), F.Id("V"));
    private static Formula Weight(Formula s) => Call("weightSpace", F.Id("h"), s);
    private static Formula LE(Formula s) => Call("weightLE", F.Id("h"), s);
    private static Formula GE(Formula s) => Call("weightGE", F.Id("h"), s);
    private static Formula Dim(Formula x) => Call("finrank", F.Id("K"), x);
    private static Formula Pow(string a, Formula r) => new Formula.Power(F.Id(a), r);
    private static Formula Twice(Formula r) => Seq(D(2), Sp, Cdot, Sp, Cast(r));
    private static Formula Plus(Formula x, Formula y) => Seq(x, Sp, F.Plus, Sp, y);
    private static Formula Minus(Formula x, Formula y) => Seq(x, Sp, F.Minus, Sp, y);
    private static Formula Negative(Formula x) => Seq(F.Minus, x);
    private static Formula Relations => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id("Sl"), D(2), F.Id("Relations"))), [F.Id("h"), F.Id("e"), F.Id("f")]);

    private static Formula CastTo(Formula x, Formula type) => Parenthesized(Seq(x, Sp, Colon, Sp, type));
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, F.Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Top => Seq(Operatorname, Grp(F.Id("top")));
    private static Formula Finset(Formula x) => Call("Finset", x);
    private static Formula Eigenspace(Formula h, Formula value) => Call("eigenspace", h, value);
    private static Formula Supremum(Formula index, Formula condition, Formula body) =>
        Call("iSup", Parenthesized(Seq(index, Sp, Colon, Sp, Ints, Sp, Mapsto, Sp,
            Call("iSup", condition, body))));
    private static Formula LinearMap(Formula scalar, Formula source, Formula target) =>
        Call("LinearMap", scalar, source, target);
    private static Formula Value(Formula fn, Formula arg) => Call("val", At(fn, arg));

    private static Formula DefinitionEnvironment(Formula body, bool charZero)
    {
        body = Assumption(Call("Module", F.Id("K"), F.Id("V")), body);
        body = Assumption(Call("AddCommGroup", F.Id("V")), body);
        body = All("V", Call("Type"), body);
        if (charZero) body = Assumption(Call("CharZero", F.Id("K")), body);
        body = Assumption(Call("Field", F.Id("K")), body);
        return All("K", Call("Type"), body);
    }

    private static Formula Endomorphism(Formula scalar) => Call("End", scalar, F.Id("V"));

    private static Formula RelationsDefinition()
    {
        var h = F.Id("h"); var e = F.Id("e"); var f = F.Id("f");
        var ef = Eq(Sub(Mul(e, f), Mul(f, e)), h);
        var he = Eq(Sub(Mul(h, e), Mul(e, h)), Seq(CastTo(D(2), F.Id("K")), Sp, Cdot, Sp, e));
        var hf = Eq(Sub(Mul(h, f), Mul(f, h)), Seq(F.Minus, CastTo(D(2), F.Id("K")), Sp, Cdot, Sp, f));
        Formula body = Iff(Relations, And(ef, And(he, hf)));
        body = All("f", Endomorphism(F.Id("K")), body);
        body = All("e", Endomorphism(F.Id("K")), body);
        body = All("h", Endomorphism(F.Id("K")), body);
        return DefinitionEnvironment(body, false);
    }

    private static Formula WeightSpaceDefinition()
    {
        var h = F.Id("h"); var s = F.Id("s");
        Formula body = Eq(Call("weightSpace", h, s), Eigenspace(h, CastTo(s, F.Id("K"))));
        body = All("s", Ints, body);
        body = All("h", Endomorphism(F.Id("K")), body);
        return DefinitionEnvironment(body, false);
    }

    private static Formula IntegralWeightsDefinition()
    {
        var h = F.Id("h"); var s = F.Id("s"); var set = F.Id("S");
        Formula body = Iff(Call("IntegralWeights", h), Some("S", Finset(Ints), Eq(
            Supremum(s, Member(s, set), Call("weightSpace", h, s)), Top)));
        body = All("h", Endomorphism(F.Id("K")), body);
        return DefinitionEnvironment(body, false);
    }

    private static Formula WeightFiltrationDefinition(bool upper)
    {
        var h = F.Id("h"); var s = F.Id("s"); var t = F.Id("t");
        var condition = upper ? Le(s, t) : Le(t, s);
        Formula body = Eq(
            Call(upper ? "weightGE" : "weightLE", h, s),
            Supremum(t, condition, Call("weightSpace", h, t)));
        body = All("s", Ints, body);
        body = All("h", Endomorphism(F.Id("K")), body);
        return DefinitionEnvironment(body, false);
    }

    private static Formula PowerMapDefinition(bool raising)
    {
        var a = F.Id("a"); var h = F.Id("h"); var e = F.Id("e"); var f = F.Id("f");
        var s = F.Id("s"); var r = F.Id("r"); var v = F.Id("v");
        var source = Call("weightSpace", h, s);
        var target = Call("weightSpace", h,
            raising ? Plus(s, Twice(r)) : Minus(s, Twice(r)));
        var map = Call(raising ? "raisingMap" : "loweringMap", a, s, r);
        var operatorPower = Parenthesized(Pow(raising ? "e" : "f", r));
        Formula type = Seq(map, Sp, Colon, Sp, LinearMap(F.Id("K"), source, target));
        Formula value = Eq(Value(map, v), At(operatorPower, Call("val", v)));
        Formula body = And(type, All("v", source, value));
        body = All("r", Nats, body);
        body = All("s", Ints, body);
        body = All("a", Relations, body);
        body = All("f", Endomorphism(F.Id("K")), body);
        body = All("e", Endomorphism(F.Id("K")), body);
        body = All("h", Endomorphism(F.Id("K")), body);
        return DefinitionEnvironment(body, true);
    }

    private static Formula Environment(Formula body, bool finite, bool sl = true, bool integral = false)
    {
        if (integral) body = Imp(Call("IntegralWeights", F.Id("h")), body);
        if (sl)
        {
            body = Imp(Relations, body);
            body = All("f", End, body);
            body = All("e", End, body);
            body = All("h", End, body);
        }
        if (finite) body = Assumption(Call("FiniteDimensional", F.Id("K"), F.Id("V")), body);
        body = Assumption(Call("Module", F.Id("K"), F.Id("V")), body);
        body = Assumption(Call("AddCommGroup", F.Id("V")), body);
        body = All("V", Call("Type"), body);
        if (sl) body = Assumption(Call("CharZero", F.Id("K")), body);
        body = Assumption(Call("Field", F.Id("K")), body);
        return All("K", Call("Type"), body);
    }
    private static Formula Shift(bool raising)
    {
        var s = F.Id("s"); var v = F.Id("v"); var r = F.Id("r");
        var target = raising ? Plus(s, Twice(r)) : Minus(s, Twice(r));
        var body = Member(At(Parenthesized(Pow(raising ? "e" : "f", r)), v), Weight(target));
        return Environment(All("s", Ints, All("v", F.Id("V"),
            Imp(Member(v, Weight(s)), All("r", Nats, body)))), false);
    }
    private static Formula Nilpotent(bool raising)
    {
        var s = F.Id("s"); var v = F.Id("v"); var n = F.Id("n");
        var body = Some("n", Nats, Eq(At(Parenthesized(Pow(raising ? "e" : "f", n)), v), D(0)));
        return Environment(All("s", Ints, All("v", F.Id("V"), Imp(Member(v, Weight(s)), body))), true);
    }
    private static Formula Injective(bool lowering)
    {
        var s = F.Id("s"); var r = F.Id("r"); var x = F.Id("x"); var y = F.Id("y");
        var power = Parenthesized(Pow(lowering ? "f" : "e", r));
        var body = All("x", Weight(s), All("y", Weight(s), Imp(Eq(At(power, Call("val", x)), At(power, Call("val", y))), Eq(x, y))));
        var bound = lowering ? Le(Cast(r), s) : Le(s, Negative(Cast(r)));
        return Environment(All("s", Ints, All("r", Nats, Imp(bound, body))), true);
    }
    private static Formula Symmetry() => Environment(All("s", Ints,
        Eq(Dim(Weight(F.Id("s"))), Dim(Weight(Negative(F.Id("s")))))), true);
    private static Formula Surjective()
    {
        var t = F.Id("t"); var r = F.Id("r"); var y = F.Id("y"); var x = F.Id("x");
        var body = Some("x", F.Id("V"), And(Member(x, Weight(Plus(t, Twice(r)))),
            Eq(At(Parenthesized(Pow("f", r)), x), y)));
        return Environment(All("t", Ints, All("r", Nats, Imp(Le(t, Negative(Cast(r))),
            All("y", F.Id("V"), Imp(Member(y, Weight(t)), body))))), true);
    }
    private static Formula RankFormula()
    {
        var r = F.Id("r");
        return Environment(All("r", Nats, Eq(Dim(Call("range", Pow("f", r))),
            Plus(Dim(GE(Cast(r))), Dim(LE(Minus(Negative(Cast(r)), D(1))))))), true, integral: true);
    }
    private static Formula FiltrationHypothesis(string name)
    {
        var s = F.Id("s");
        return All("s", Ints, Le(Call("map", At(F.Id(name), s), F.Id("T")), At(F.Id(name), Minus(s, D(2)))));
    }
    private static Formula FiltrationPower()
    {
        var s = F.Id("s"); var r = F.Id("r");
        var body = All("s", Ints, All("r", Nats,
            Le(Call("map", At(F.Id("F"), s), Pow("T", r)), At(F.Id("F"), Minus(s, Twice(r))))));
        return Environment(All("F", Parenthesized(
                new Formula.TypeArrow(Ints, Call("Submodule", F.Id("K"), F.Id("V")))),
            All("T", End, Imp(FiltrationHypothesis("F"), body))), false, sl: false);
    }
    private static Formula Comparison()
    {
        var s = F.Id("s"); var r = F.Id("r");
        var hyp = All("s", Ints, Le(Call("map", LE(s), F.Id("T")), LE(Minus(s, D(2)))));
        var body = All("r", Nats, Le(Dim(Call("range", Pow("T", r))), Dim(Call("range", Pow("f", r)))));
        return Environment(All("T", End, Imp(hyp, body)), true, integral: true);
    }

    private static Formula EigenspaceComparison()
    {
        var s = F.Id("s"); var r = F.Id("r"); var m = F.Id("m"); var u = F.Id("U");
        var w = Eigenspace(u, m);
        var restrictedT = Call("restrict", F.Id("T"), w);
        var restrictedF = Call("restrict", F.Id("f"), w);
        Formula body = All("m", F.Id("K"), All("r", Nats,
            Le(Dim(Call("range", new Formula.Power(Parenthesized(restrictedT), r))),
                Dim(Call("range", new Formula.Power(Parenthesized(restrictedF), r))))));
        body = Imp(Call("Commute", u, F.Id("T")), body);
        body = Imp(Call("Commute", u, F.Id("f")), body);
        body = Imp(Call("Commute", u, F.Id("e")), body);
        body = Imp(Call("Commute", u, F.Id("h")), body);
        var hyp = All("s", Ints, Le(Call("map", LE(s), F.Id("T")), LE(Minus(s, D(2)))));
        return Environment(All("U", End, All("T", End, Imp(hyp, body))), true, integral: true);
    }
}
