using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class CARRevelationScalingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixing CAR experiments with complete revelation scales both directed deficiencies exactly "
            + "and gives ordinary partition realizations on one public product seed.",
        H("Exact CAR revelation scaling"),
        Blocks(Describe.Lean(
            DescribeId.Create("car-revelation-scaling"),
            DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/CARRevelationScaling.result"),
            H("Two directed equalities and a common partition seed"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A is an arbitrary finite nonempty state type at any universe level u, "
                    + "with decidable equality, and n is its cardinality. Block(A) is the alphabet "
                    + "of all nonempty finite subsets of A. The profiles w and v take arbitrary nonnegative "
                    + "real values, and each CAR row sums to one. The row(u,i,B) equals u(B) if i "
                    + "belongs to B and zero otherwise. Singleton and zero-weight blocks remain in this alphabet.")),
                Paragraph(Text("finiteDeficiency takes the target first and the source second. It minimizes "
                    + "the maximum statewise half-L1 error over all stochastic kernels on the full alphabet. "
                    + "One kernel is used for every state; its output rows may assign mass to zero-weight "
                    + "target blocks and to blocks that do not contain the true state. No support restriction "
                    + "or prior is imposed on this minimization.")),
                new DocumentBlock.DisplayFormula(DeficiencyFormula()),
                Paragraph(Text("The function M mixes a profile with complete revelation: the "
                    + "revealing profile is one on every singleton and zero on every larger block. Both "
                    + "equalities hold for every real t between zero and one, with multiplication by ofReal(t) "
                    + "in the extended nonnegative reals. For n = 1 the only block is the unique singleton, "
                    + "both original profiles have weight one, and both original deficiencies vanish.")),
                Paragraph(Text("Finite Bayes minima are attained. For a probability prior mu, a finite "
                    + "nonempty action set D, and a loss l between zero and one, choose at each observation "
                    + "an action minimizing its finite sum of weighted losses. The resulting deterministic "
                    + "decision rule is stochastic and no randomized rule has a smaller cost. For a CAR "
                    + "profile u this choice separates block by block: H(B) is independent of u, including "
                    + "when u(B) is zero. Thus the same H applies to both profiles and their revealing mixtures.")),
                new DocumentBlock.DisplayFormula(BlockRiskFormula()),
                Paragraph(Text("To obtain a shared optimizing kernel and task, take stochastic experiments "
                    + "X and Y on O = Block(A). The kernel domain is the finite product of probability "
                    + "simplexes, and the second domain is the probability simplex on A times Finset(O). "
                    + "The displayed payoff is continuous and affine in each variable. These nonempty "
                    + "compact convex domains admit an actual Sion saddle (Kstar,zstar). The saddle "
                    + "inequalities hold for every kernel K and every state-event probability vector z.")),
                new DocumentBlock.DisplayFormula(SaddleFormula()),
                Paragraph(Text("Sum zstar over events to obtain the prior mu, and over events containing "
                    + "an output letter to obtain g. Then zero is at most g(i,C) and g(i,C) is at most mu(i). "
                    + "The loss is g(i,C)/mu(i) for positive mu(i), and zero when mu(i) is zero. In the latter "
                    + "case g(i,C) is also zero, so mu(i) l(i,C) = g(i,C) holds without discarding any state.")),
                new DocumentBlock.DisplayFormula(SaddleTaskFormula()),
                Paragraph(Text("The positive-difference event of each simulated row realizes its "
                    + "half-L1 distance from the target row. Testing the saddle against these events and "
                    + "an attained Bayes decision bounds every state error of Kstar by the same task's "
                    + "Bayes-risk gap. Bounded-loss risk transport gives the converse bound by deficiency, "
                    + "and the defining infimum bounds deficiency by the error of Kstar. All three values "
                    + "are equal. Probability rows bound deficiency by one, and the attained nonnegative "
                    + "Bayes costs are finite, so the conversions to real values in these formulas are valid.")),
                new DocumentBlock.DisplayFormula(AttainmentFormula()),
                Paragraph(Text("For each fixed task, the complete-revelation contribution in the block "
                    + "risk formula is identical for w and v and cancels. Apply the attained task for the "
                    + "mixed experiments to bound their deficiency above by t times the original deficiency. "
                    + "Apply the attained task for the original experiments to the mixed ones to obtain "
                    + "the reverse inequality. Interchanging w and v proves the second directed equality. "
                    + "This argument includes t = 0 and never divides by t; no duality or attainment "
                    + "hypothesis is required.")),
                new DocumentBlock.DisplayFormula(RiskScalingFormula()),
                Paragraph(Text("For the partition construction suppose n is at least two and "
                    + "0 <= t <= 2/n, which also implies t <= 1. For either original profile u, let S(u) "
                    + "be the total weight of nonsingleton blocks. Summing the CAR row equations over "
                    + "states counts each block weight once per member. Nonnegativity and the size of "
                    + "each nonsingleton give S(u) <= n/2, hence t S(u) <= 1.")),
                new DocumentBlock.DisplayFormula(MassFormula()),
                Paragraph(Text("For every nonempty block B form the ordinary partition with B as one "
                    + "part and each state outside B as its own singleton part. These parts are nonempty, "
                    + "pairwise disjoint, and have union A. Let T(none) be the discrete partition and "
                    + "T(some(B)) this partition. The selector law q(u) gives mass t u(B) to some(B) "
                    + "when B is nonsingleton, zero to singleton selectors, and the residual mass "
                    + "1 - t S(u) to none. All masses are nonnegative and their sum is one.")),
                new DocumentBlock.DisplayFormula(SelectorFormula()),
                Paragraph(Text("A nonsingleton block B occurs with total probability t u(B). A singleton "
                    + "{i} occurs under the discrete selector and under exactly those nonsingleton "
                    + "selectors whose block omits i. The CAR row equation gives its probability "
                    + "1 - t + t u({i}). Thus the induced profile is exactly M(t,u) on every block.")),
                new DocumentBlock.DisplayFormula(SingletonFormula()),
                Paragraph(Text("Use the actual product law of the two selector laws on "
                    + "Seed = Option(Block(A)) times Option(Block(A)). Define P from its first coordinate "
                    + "and Q from its second. The law is independent of the state, nonnegative, and of "
                    + "total mass one; its induced profiles are M(t,w) and M(t,v), respectively. Both "
                    + "experiments reveal the entire same seed r, together with the part containing the "
                    + "state. The common seed and the partition realizations are constructed, not assumed.")),
                new DocumentBlock.DisplayFormula(ProductFormula()),
                Paragraph(Text("The experiment E(p,T) assigns p(r) to the output (r,B) precisely when "
                    + "B is the part of T(r) containing the state. For each of T = P and T = Q separately, "
                    + "let h be its induced profile, respectively M(t,w) and M(t,v). Forgetting the seed "
                    + "uses the deterministic kernel F((r,C),B) = indicator(C = B). For reconstruction, "
                    + "choose a fixed state iota and output ostar = ((none,none),{iota}) to complete each "
                    + "zero-weight input row. Positive-weight input rows condition the entire seed on "
                    + "the event that B is a part of T(r), while keeping the observed block.")),
                new DocumentBlock.DisplayFormula(KernelsFormula()),
                Paragraph(Text("The induced-profile equation makes each positive reconstruction row "
                    + "sum to one. If h(B) = 0 and B is a part of T(r), nonnegativity gives "
                    + "0 <= p(r) <= h(B), hence p(r) = 0. This proves the reconstruction identity also "
                    + "on zero-weight blocks, while the fixed point mass makes those kernel rows "
                    + "stochastic. Finally, B is the part containing i exactly when B is a part and "
                    + "i belongs to B. This gives both exact channelOutput identities for P and both "
                    + "for Q. At t = 0 the product law concentrates on (none,none), so the same "
                    + "construction covers complete revelation without a positive-t assumption."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula A = F.Id("A"), w = F.Id("w"), v = F.Id("v"), B = F.Id("B"), i = F.Id("i");
        Formula t = F.Id("t"), u = F.Id("u"), n = F.Id("n"), M = F.Id("M"), seed = F.Id("Seed");
        Formula p = F.Id("p"), P = F.Id("P"), Q = F.Id("Q"), r = F.Id("r"), E = F.Id("E");
        Formula blocks = Call("Block", A), profile = Arrow(blocks, Real());
        Formula partitions = Call("Finpartition", Typed(Call("univ"), Call("Finset", A)));
        Formula selectors = Arrow(seed, partitions);
        Formula hypotheses = And(
            All(B, blocks, LeF(D(0), Apply(w, B))), All(B, blocks, LeF(D(0), Apply(v, B))),
            All(i, A, Eqn(SumOver(Typed(B, blocks), Call("row", w, i, B)), D(1))),
            All(i, A, Eqn(SumOver(Typed(B, blocks), Call("row", v, i, B)), D(1))));
        Formula Scaling(Formula source, Formula target) => Eqn(
            Call("finiteDeficiency", Call("row", Apply(M, t, target)), Call("row", Apply(M, t, source))),
            Mul(Call("ofReal", t), Call("finiteDeficiency", Call("row", target), Call("row", source))));
        Formula Profile(Formula T, Formula profileValue) => All(B, blocks, Eqn(
            SumOver(Typed(r, seed), Ite(Member(B, Call("parts", Apply(T, r))), Apply(p, r), D(0))),
            Apply(M, t, profileValue, B)));
        Formula Channels(Formula T, Formula profileValue)
        {
            Formula Fk = F.Id("F"), Rk = F.Id("R"), outputs = Product(seed, blocks);
            return Some(Fk, Call("FiniteMarkovKernel", outputs, blocks),
                Some(Rk, Call("FiniteMarkovKernel", blocks, outputs), And(
                    All(i, A, Eqn(Call("channelOutput", Projection(Fk), Apply(E, p, T, i)),
                        Call("row", Apply(M, t, profileValue), i))),
                    All(i, A, Eqn(Call("channelOutput", Projection(Rk), Call("row", Apply(M, t, profileValue), i)),
                        Apply(E, p, T, i))))));
        }
        Formula conclusions = And(
            All(t, Real(), Implies(LeF(D(0), t), LeF(t, D(1)), And(Scaling(w, v), Scaling(v, w)))),
            Implies(Eqn(n, D(1)), And(
                Eqn(Call("finiteDeficiency", Call("row", v), Call("row", w)), D(0)),
                Eqn(Call("finiteDeficiency", Call("row", w), Call("row", v)), D(0)))),
            Implies(LeF(D(2), n), All(t, Real(), Implies(LeF(D(0), t), LeF(t, Div(D(2), n)),
                Some(p, Arrow(seed, Real()), Some(P, selectors, Some(Q, selectors, And(
                    All(r, seed, LeF(D(0), Apply(p, r))), Eqn(SumOver(Typed(r, seed), Apply(p, r)), D(1)),
                    Profile(P, w), Profile(Q, v), Channels(P, w), Channels(Q, v)))))))));
        Formula definitions = LetIn([
            Eqn(n, Call("card", A)),
            Eqn(M, Lambda(CommaList(Typed(t, Real()), Typed(u, profile), Typed(B, blocks)),
                Add(Mul(Paren(Sub(D(1), t)), Ite(Eqn(Call("card", B), D(1)), D(1), D(0))),
                    Mul(t, Apply(u, B))))),
            Eqn(seed, Product(Call("Option", blocks), Call("Option", blocks))),
            Eqn(E, Lambda(CommaList(Typed(p, Arrow(seed, Real())), Typed(P, selectors), Typed(i, A),
                    Typed(Pair(r, B), Product(seed, blocks))),
                Ite(Eqn(Call("part", Apply(P, r), i), B), Apply(p, r), D(0))))], conclusions);
        return Display(All(A, new Formula.Subscript(F.Id("Type"), F.Id("u")),
            Implies(Call("Fintype", A), Call("DecidableEq", A), Call("Nonempty", A),
                All(w, profile, All(v, profile, Implies(hypotheses, definitions))))));
    }

    private static Formula DeficiencyFormula()
    {
        Formula A = F.Id("A"), X = F.Id("X"), Y = F.Id("Y"), K = F.Id("K"), i = F.Id("i"), B = F.Id("B");
        Formula blocks = Call("Block", A);
        Formula error = Mul(Div(D(1), D(2)), SumOver(Typed(B, blocks),
            Abs(Sub(Apply(Y, i, B), Apply(Call("channelOutput", Projection(K), Apply(X, i)), B)))));
        return Display(Eqn(Call("finiteDeficiency", Y, X), Call("iInf",
            Lambda(Typed(K, Call("FiniteMarkovKernel", blocks, blocks)),
                Call("ofReal", Call("max", i, A, error))))));
    }

    private static Formula BlockRiskFormula()
    {
        Formula B = F.Id("B"), i = F.Id("i"), a = F.Id("a"), mu = F.Id("mu"), l = F.Id("l"), u = F.Id("u");
        return Display(Lines(
            Eqn(Call("H", B), Call("min", a, F.Id("D"), SumOver(Member(i, B), Mul(Apply(mu, i), Apply(l, i, a))))),
            Eqn(Call("toReal", Call("finiteBayesRisk", mu, l, Call("row", u))),
                SumOver(Typed(B, Call("Block", F.Id("A"))), Mul(Apply(u, B), Call("H", B))))));
    }

    private static Formula SaddleFormula()
    {
        Formula K = F.Id("K"), z = F.Id("z"), i = F.Id("i"), S = F.Id("S"), C = F.Id("C"), O = F.Id("O");
        Formula ks = F.Id("Kstar"), zs = F.Id("zstar");
        return Display(Lines(
            Eqn(Call("f", K, z), SumOver(Typed(i, F.Id("A")), SumOver(Typed(S, Call("Finset", O)),
                Mul(Apply(z, Pair(i, S)), SumOver(Member(C, S), Sub(
                    Apply(Call("channelOutput", Projection(K), Apply(F.Id("X"), i)), C), Apply(F.Id("Y"), i, C))))))),
            LeF(Call("f", ks, z), Call("f", ks, zs)), LeF(Call("f", ks, zs), Call("f", K, zs))));
    }

    private static Formula SaddleTaskFormula()
    {
        Formula i = F.Id("i"), C = F.Id("C"), S = F.Id("S"), zs = F.Id("zstar"), mu = F.Id("mu"), g = F.Id("g"), l = F.Id("l");
        Formula events = Call("Finset", F.Id("O"));
        return Display(Lines(
            Eqn(Apply(mu, i), SumOver(Typed(S, events), Apply(zs, Pair(i, S)))),
            Eqn(Apply(g, i, C), SumOver(Typed(S, events), Ite(Member(C, S), Apply(zs, Pair(i, S)), D(0)))),
            Eqn(Apply(l, i, C), Ite(Eqn(Apply(mu, i), D(0)), D(0), Div(Apply(g, i, C), Apply(mu, i)))),
            Eqn(Mul(Apply(mu, i), Apply(l, i, C)), Apply(g, i, C))));
    }

    private static Formula AttainmentFormula()
    {
        Formula X = F.Id("X"), Y = F.Id("Y"), mu = F.Id("mu"), l = F.Id("l");
        Formula value = Call("toReal", Call("finiteDeficiency", Y, X));
        return Display(Lines(
            Eqn(Call("uniformSimulationError", Y, X, F.Id("Kstar")), value),
            Eqn(value, Sub(Call("toReal", Call("finiteBayesRisk", mu, l, X)),
                Call("toReal", Call("finiteBayesRisk", mu, l, Y))))));
    }

    private static Formula RiskScalingFormula()
    {
        Formula t = F.Id("t"), w = F.Id("w"), v = F.Id("v");
        Formula Risk(Formula profile) => Call("toReal", Call("finiteBayesRisk", F.Id("mu"), F.Id("l"), Call("row", profile)));
        return Display(Eqn(Sub(Risk(Call("M", t, w)), Risk(Call("M", t, v))),
            Mul(t, Paren(Sub(Risk(w), Risk(v))))));
    }

    private static Formula MassFormula()
    {
        Formula u = F.Id("u"), B = F.Id("B"), blocks = Call("Block", F.Id("A"));
        Formula mass = Call("S", u), total = SumOver(Typed(B, blocks), Mul(Call("card", B), Apply(u, B)));
        return Display(Lines(
            Eqn(mass, SumOver(Typed(B, blocks), Ite(LeF(D(2), Call("card", B)), Apply(u, B), D(0)))),
            LeF(Mul(D(2), mass), total), Eqn(total, F.Id("n")),
            LeF(mass, Div(F.Id("n"), D(2))), LeF(Mul(F.Id("t"), mass), D(1))));
    }

    private static Formula SelectorFormula()
    {
        Formula u = F.Id("u"), B = F.Id("B"), t = F.Id("t"), i = F.Id("i");
        Formula none = Call("none"), some = Call("some", B);
        Formula outside = Seq(OpenBrace, Call("singleton", i), Sp, Mid, Sp,
            Member(i, F.Id("A")), Comma, Sp, Call("not", Member(i, B)), CloseBrace);
        return Display(Lines(
            Eqn(Call("T", none), Call("discrete", F.Id("A"))),
            Eqn(Call("parts", Call("T", some)), Call("union", Call("singleton", B), outside)),
            Eqn(Call("q", u, none), Sub(D(1), Mul(t, Call("S", u)))),
            Eqn(Call("q", u, some), Ite(LeF(D(2), Call("card", B)), Mul(t, Apply(u, B)), D(0)))));
    }

    private static Formula SingletonFormula()
    {
        Formula i = F.Id("i"), B = F.Id("B"), u = F.Id("u"), t = F.Id("t");
        Formula outside = SumOver(Typed(B, Call("Block", F.Id("A"))),
            Ite(AndInline(LeF(D(2), Call("card", B)), Call("not", Member(i, B))), Apply(u, B), D(0)));
        return Display(Eqn(Add(Sub(D(1), Mul(t, Call("S", u))), Mul(t, outside)),
            Add(Sub(D(1), t), Mul(t, Apply(u, Call("singleton", i))))));
    }

    private static Formula ProductFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), r = F.Id("r"), B = F.Id("B"), i = F.Id("i"), T = F.Id("T");
        return Display(Lines(
            Eqn(Call("p", Pair(a, b)), Mul(Call("q", F.Id("w"), a), Call("q", F.Id("v"), b))),
            Eqn(Call("P", Pair(a, b)), Call("T", a)), Eqn(Call("Q", Pair(a, b)), Call("T", b)),
            Eqn(Call("E", F.Id("p"), T, i, Pair(r, B)),
                Ite(Eqn(Call("part", Apply(T, r), i), B), Call("p", r), D(0)))));
    }

    private static Formula KernelsFormula()
    {
        Formula B = F.Id("B"), C = F.Id("C"), r = F.Id("r"), h = F.Id("h"), T = F.Id("T");
        Formula output = Pair(r, C), ostar = F.Id("ostar");
        return Display(Lines(
            Eqn(ostar, Pair(Pair(Call("none"), Call("none")), Call("singleton", F.Id("iota")))),
            Eqn(Call("F", output, B), Ite(Eqn(C, B), D(1), D(0))),
            Eqn(Call("R", B, output), Ite(Eqn(Apply(h, B), D(0)), Ite(Eqn(ostar, output), D(1), D(0)),
                Ite(AndInline(Eqn(B, C), Member(B, Call("parts", Apply(T, r)))),
                    Div(Call("p", r), Apply(h, B)), D(0))))));
    }

    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(Seq(Operatorname, Grp(F.Id(name))), args);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula All(Formula value, Formula type, Formula body) => Seq(Forall, Sp, Typed(value, type), Comma, Sp, body);
    private static Formula Some(Formula value, Formula type, Formula body) => Seq(Exists, Sp, Typed(value, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Paren(CommaList(a, b));
    private static Formula Lambda(Formula args, Formula body) => Paren(Seq(args, Sp, Mapsto, Sp, body));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Projection(Formula value) => Seq(value, Dot, D(1));
    private static Formula Ite(Formula condition, Formula yes, Formula no) => Call("ite", condition, yes, no);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeF(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula SumOver(Formula index, Formula body) => Seq(new Formula.Subscript(Sum, Grp(index)), Sp, Grp(body));
    private static Formula Display(Formula body) => Disp(Seq(Begin, Grp(F.Id("gathered")), body, End, Grp(F.Id("gathered"))));
    private static Formula Add(params Formula[] terms) => Infix(Plus, terms);
    private static Formula Sub(params Formula[] terms) => Infix(Minus, terms);
    private static Formula Mul(params Formula[] terms) => Infix(Cdot, terms);
    private static Formula CommaList(params Formula[] terms) => Infix(Comma, terms);
    private static Formula AndInline(params Formula[] clauses) => Paren(Infix(Land, clauses));
    private static Formula Infix(Formula op, Formula[] terms)
    {
        var items = new List<Formula>();
        for (var i = 0; i < terms.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, op, Sp]);
            items.Add(terms[i]);
        }
        return Seq([.. items]);
    }
    private static Formula Lines(params Formula[] clauses) => Infix(Seq(RowBreak, Grp()), clauses);
    private static Formula And(params Formula[] clauses) =>
        Paren(Infix(Seq(Land, RowBreak, Grp()), clauses.Select(Paren).ToArray()));
    private static Formula Implies(params Formula[] clauses) =>
        Infix(Seq(Rightarrow, RowBreak, Grp()), clauses.Select(Paren).ToArray());
    private static Formula LetIn(Formula[] definitions, Formula body) => Seq(
        F.Text, Grp(F.Id("let"), Sp), Lines(definitions), RowBreak, Grp(),
        F.Text, Grp(F.Id("in"), Sp), body);
}
