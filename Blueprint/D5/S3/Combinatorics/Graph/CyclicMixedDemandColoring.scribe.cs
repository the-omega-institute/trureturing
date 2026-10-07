using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CyclicMixedDemandColoringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed singleton and double demands on a cyclic distance graph have an exact slot-coloring minimum.",
        H("Cyclic mixed-demand coloring"),
        Blocks(
            Paragraph(Text("In the formulas, div denotes natural-number division, mod denotes natural remainder, and subtraction on natural numbers is truncated. Angle brackets construct a finite value; proof arguments of cyclicIndex are suppressed under the displayed size inequality.")),
            Paragraph(Text("The packing and slot constructions assume 0<m<=n. Demands are positive "
                + "and at most two in the mixed minimum; the general slot theorem allows larger finite demands.")),
            Definition("vertices", "Vertex", "Demand types",
                "There are n cyclic prefixes. Prefix t has k(t) types, indexed by Fin(k(t)). "
                + "A vertex is a prefix together with a type rank. Rank zero is used for every singleton, "
                + "independently of any external label attached to that singleton."),
            Definition("near", "Near", "Integer circular adjacency",
                "Two prefixes are near when their integer circular distance is strictly less than m. "
                + "The definition includes the ordinary interval and both orientations across the seam. "
                + "For positive m a prefix is near itself."),
            Definition("proper", "Proper", "Proper demand coloring",
                "A coloring separates every pair of distinct types whose prefixes are near. "
                + "For m>0, all types at a single prefix have different colors."),
            Claim("packing", "separated_packing", "Cyclic packing",
                "For 0<m<=n, every finite set of pairwise separated types has cardinality at most floor(n/m). "
                + "Attach the next m cyclic positions to each selected type. These intervals are disjoint: "
                + "an intersection forces near prefixes, and different types at one prefix are also forbidden. "
                + "Their injection into the n positions gives m times the cardinality at most n. "
                + "The argument includes empty sets, singleton sets, and intervals crossing the seam."),
            Claim("total-packing", "packing_lower_bound", "Total demand bound",
                "For 0<m<=n, every proper coloring with c colors satisfies sum(k)<=c floor(n/m). "
                + "Partition the types by color and apply the cyclic packing bound to every color class."),
            Definition("window", "Window", "Wrapping block sums",
                "A cumulative boundary function s represents the slot blocks. A nonwrapping m-block sum "
                + "is s(i+m)-s(i). A wrapping sum is s(n)-s(i)+s(i+m-n)-s(0)."),
            Claim("slot-coloring", "cyclic_slot_coloring", "Cyclic slot validity",
                "Assume 0<m<=n, c>0, s(0)=0, strictly positive blocks s(i+1)-s(i), "
                + "k(i)<=s(i+1)-s(i), c divides s(n), and every wrapping m-block sum is at most c. "
                + "Color rank r at prefix i by (s(i)+r) mod c. For an adjacent ordered pair, selected slots "
                + "are strictly ordered and less than c apart. Across the seam translate the second slot "
                + "by s(n), which preserves its residue. Distinct ranks in one block are handled by the same "
                + "strict bound. Thus the coloring is proper, including equality of a window sum with c."),
            Claim("low-slot-formula", "low_slot_formula_valid", "Exact shortened-slot formula",
                "For the shortened singleton blocks, the displayed cumulative formula starts at zero, "
                + "has length one exactly on R and length two elsewhere, ends at 2ma, and its chosen "
                + "slot residues form a proper coloring. The existential constructor uses this coloring."),
            Claim("low-slots", "low_slot_construction", "Shortened singleton blocks",
                "Assume 0<m<=n, n=ma+rho, and every demand is one or two. Choose a set R "
                + "of exactly 2rho singleton prefixes. Set s(i)=2i-#{r in R:r<i}. "
                + "Each chosen block has length one; every other block has length two. All demands are "
                + "contained, the total is 2ma, and every wrapping m-block sum is at most 2m. "
                + "Cyclic slot validity supplies 2m colors for any placement of the chosen singleton prefixes."),
            Claim("low-branch", "low_branch_coloring", "The low branch",
                "Assume 0<m<=n, n=ma+rho, and every demand is one or two. If there are at "
                + "least 2rho singleton prefixes, select exactly 2rho of them and use "
                + "the shortened-block construction. No contiguous placement condition is imposed on the singletons."),
            Claim("spaced-slots", "spaced_slot_construction", "Spaced extra slots",
                "Assume 0<m<=n and every demand is at most two. Start with blocks of length two "
                + "and add one slot at each prefix in a cyclically m-separated set R. "
                + "Set s(i)=2i+#{r in R:r<i}. Every wrapping m-window contains at most one extra slot, "
                + "so its sum is at most 2m+1. If 2m+1 divides 2n+|R|, this gives a proper coloring with 2m+1 colors."),
            Claim("high-slot-formula", "high_slot_formula_valid", "Exact spaced-slot formula",
                "With c=2m+1, z=(a-2rho) mod c, and R={qm:0<=q<z}, the cumulative formula "
                + "starts at zero, ends at 2n+z, and its chosen slot residues form a proper coloring. "
                + "The high-branch constructor uses this coloring."),
            Claim("high-branch", "high_branch_coloring", "The high branch",
                "Assume 0<m<=n, n=ma+rho, a>=2rho, and every demand is at most two. "
                + "Put c=2m+1 and z=(a-2rho) mod c. Add slots at "
                + "0,m,...,(z-1)m. Since z<=a, consecutive extras and the cyclic closing gap are at least m apart. "
                + "The identity 2n+(a-2rho)=ca shows that c divides 2n+z. This construction allows arbitrary "
                + "singleton positions and even applies when every demand is two."),
            Definition("cyclic-index", "cyclicIndex", "A cyclic consecutive window",
                "The offset i from start is start+i when this is below n, and start+i-n otherwise. "
                + "Offsets range over Fin(m), with m<=n, so there is at most one seam crossing."),
            Claim("double-window", "double_window_lower_bound", "The double-demand clique",
                "If an m-consecutive cyclic window consists entirely of double-demand prefixes, its 2m types "
                + "form a clique. Their colors are distinct, giving c>=2m for every proper coloring."),
            Claim("minimum", "mixed_demand_minimum", "The exact mixed minimum",
                "Assume m>=2, n>2m, n=ma+rho, rho<m, a>=2rho, demands k(t) in {1,2}, "
                + "and one m-consecutive all-double window. Let L be the number of singleton prefixes. "
                + "The least feasible number of colors is max(2m,ceil((2n-L)/a)), exactly "
                + "2m+1 when L<2rho and 2m otherwise. Natural ceiling is represented by (2n-L+a-1)/a; "
                + "the hypotheses imply a>0. The clique gives the 2m lower bound, packing uses "
                + "floor(n/m)=a and total demand 2n-L, and the two slot constructions attain the stated bound. "
                + "This is a theorem about cyclic demand types; additional physical observation data require their own correspondence."))));

    private static DocumentBlock Definition(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create("cyclic-mixed-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Claim(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create("cyclic-mixed-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula Q(string names, Formula type, Formula body)
    {
        var binders = names.Split(' ');
        for (var i = binders.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, V(binders[i]), Colon, Sp, Par(type), Comma, Sp, Par(body));
        return body;
    }
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, Par(type), Comma, Sp, Par(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, Sp, Par(type), Sp, Mapsto, Sp, Par(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(V("let"), Sp, V(name), Colon, Sp, type, Sp, Colon, Eq, Sp, value, Semi, Sp, Par(body));
    private static Formula Arr(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, Par(b));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffF(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] parts)
    {
        var result = parts[parts.Length - 1];
        for (var i = parts.Length - 2; i >= 0; i--) result = Seq(Par(parts[i]), Sp, Land, Sp, Par(result));
        return result;
    }
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Not(Formula a) => Seq(Neg, Par(a));
    private static Formula Add(Formula a, Formula b) => Seq(Par(a), Sp, Plus, Sp, Par(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Par(a), Sp, Minus, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Div(Formula a, Formula b) => Call("div", a, b);
    private static Formula Mod(Formula a, Formula b) => Call("mod", a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Member(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula Set(string name, Formula type, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Choice(Formula test, Formula yes, Formula no) =>
        Seq(V("if"), Sp, test, Sp, V("then"), Sp, yes, Sp, V("else"), Sp, no);

    private static Formula Statement(string declaration)
    {
        var n = V("n"); var m = V("m"); var a = V("a"); var rho = V("rho");
        var k = V("k"); var c = V("c"); var color = V("color"); var t = V("t");
        var i = V("i"); var j = V("j"); var x = V("x"); var y = V("y");
        var s = V("s"); var set = V("S"); var removed = V("R"); var start = V("start");
        var vertex = Call("Vertex", k);
        var demandType = Arr(Fin(n), N);
        var proper = Call("Proper", m, k, color);
        var bounds = And(Less(D(0), m), Leq(m, n));
        var decomposition = Eqn(n, Add(Mul(m, a), rho));
        var demands = Q("t", Fin(n), Or(Eqn(Call("k", t), D(1)), Eqn(Call("k", t), D(2))));
        var atMostTwo = Q("t", Fin(n), Leq(Call("k", t), D(2)));
        var singletonCount = Card(Call("filter", Call("univ", Fin(n)), Fn("t", Fin(n), Eqn(Call("k", t), D(1)))));
        var within = Seq(removed, Sp, Subseteq, Sp, Call("range", n));
        var hasColor = Ex("color", Arr(vertex, Fin(c)), proper);
        var near = Or(And(Less(Val(i), Add(Val(j), m)), Less(Val(j), Add(Val(i), m))),
            Or(Less(Add(n, Val(i)), Add(Val(j), m)), Less(Add(n, Val(j)), Add(Val(i), m))));
        var separatedR = Q("x y", N, Imp(And(Member(x, removed), Member(y, removed), Ne(x, y)),
            Not(Or(And(Less(x, Add(y, m)), Less(y, Add(x, m))),
                Or(Less(Add(n, x), Add(y, m)), Less(Add(n, y), Add(x, m)))))));
        Formula result;
        if (declaration == "Vertex")
        {
                result = Q("n", N, Q("k", demandType,
                    Eqn(vertex, Seq(Sigma, Underscore, Grp(Seq(t, Colon, Fin(n))), Sp, Fin(Call("k", t))))));
        }
        else if (declaration == "Near")
        {
                result = Q("n m", N, Q("i j", Fin(n), IffF(Call("Near", m, i, j), near)));
        }
        else if (declaration == "Proper")
        {
                result = Q("n m", N, Q("Z", V("Type"), Q("k", demandType,
                    Q("color", Arr(vertex, V("Z")), IffF(proper,
                        Q("x y", vertex, Imp(And(Ne(x, y), Call("Near", m, Call("fst", x), Call("fst", y))),
                            Ne(Call("color", x), Call("color", y)))))))));
        }
        else if (declaration == "separated_packing")
        {
                result = Q("n m", N, Q("k", demandType, Q("S", Call("Finset", vertex),
                    Imp(And(bounds, Q("x y", vertex, Imp(And(Member(x, set), Member(y, set), Ne(x, y)),
                        Not(Call("Near", m, Call("fst", x), Call("fst", y)))))), Leq(Card(set), Div(n, m))))));
        }
        else if (declaration == "packing_lower_bound")
        {
                result = Q("n m c", N, Q("k", demandType, Q("color", Arr(vertex, Fin(c)),
                    Imp(And(bounds, proper), Leq(Call("sum", Call("univ", Fin(n)), k), Mul(c, Div(n, m)))))));
        }
        else if (declaration == "Window")
        {
                result = Q("n m i", N, Q("s", Arr(N, N), Eqn(Call("Window", n, m, s, i),
                    Choice(Leq(Add(i, m), n), Sub(Call("s", Add(i, m)), Call("s", i)),
                        Sub(Add(Sub(Call("s", n), Call("s", i)), Call("s", Sub(Add(i, m), n))), Call("s", D(0)))))));
        }
        else if (declaration == "cyclic_slot_coloring")
        {
                var slotColor = Fn("x", vertex, Seq(Langle, Mod(Add(Call("s", Val(Call("fst", x))), Val(Call("snd", x))), c), Rangle, Colon, Fin(c)));
                result = Q("n m c", N, Q("k", demandType, Q("s", Arr(N, N), Imp(And(bounds, Less(D(0), c),
                    Eqn(Call("s", D(0)), D(0)), Q("i", N, Imp(Less(i, n), Less(Call("s", i), Call("s", Add(i, D(1)))))),
                    Q("t", Fin(n), Leq(Call("k", t), Sub(Call("s", Add(Val(t), D(1))), Call("s", Val(t))))),
                    Eqn(Mod(Call("s", n), c), D(0)), Q("i", N, Imp(Less(i, n), Leq(Call("Window", n, m, s, i), c)))),
                    Call("Proper", m, k, slotColor)))));
        }
        else if (declaration == "low_slot_formula_valid")
        {
                var boundary = Fn("i", N, Sub(Mul(D(2), i),
                    Card(Call("filter", removed, Fn("t", N, Less(t, i))))));
                var slotColor = Fn("x", vertex, Seq(Langle,
                    Mod(Add(Call("s", Val(Call("fst", x))), Val(Call("snd", x))), Mul(D(2), m)),
                    Rangle, Colon, Fin(Mul(D(2), m))));
                result = Q("n m a rho", N, Q("k", demandType, Q("R", Call("Finset", N),
                    Imp(And(bounds, decomposition, demands, within, Eqn(Card(removed), Mul(D(2), rho)),
                        Q("t", Fin(n), Imp(Member(Val(t), removed), Eqn(Call("k", t), D(1))))),
                        Let("s", Arr(N, N), boundary, And(Eqn(Call("s", D(0)), D(0)),
                            Q("i", N, Eqn(Sub(Call("s", Add(i, D(1))), Call("s", i)),
                                Choice(Member(i, removed), D(1), D(2)))),
                            Eqn(Call("s", n), Mul(Mul(D(2), m), a)),
                            Call("Proper", m, k, slotColor)))))));
        }
        else if (declaration == "low_slot_construction")
        {
                result = Q("n m a rho", N, Q("k", demandType, Q("R", Call("Finset", N),
                    Imp(And(bounds, decomposition, demands, within, Eqn(Card(removed), Mul(D(2), rho)),
                        Q("t", Fin(n), Imp(Member(Val(t), removed), Eqn(Call("k", t), D(1))))),
                        Ex("color", Arr(vertex, Fin(Mul(D(2), m))), proper)))));
        }
        else if (declaration == "low_branch_coloring")
        {
                result = Q("n m a rho", N, Q("k", demandType,
                    Imp(And(bounds, decomposition, demands, Leq(Mul(D(2), rho), singletonCount)),
                        Ex("color", Arr(vertex, Fin(Mul(D(2), m))), proper))));
        }
        else if (declaration == "spaced_slot_construction")
        {
                result = Q("n m", N, Q("k", demandType, Q("R", Call("Finset", N),
                    Imp(And(bounds, atMostTwo, within, separatedR,
                        Eqn(Mod(Add(Mul(D(2), n), Card(removed)), Add(Mul(D(2), m), D(1))), D(0))),
                        Ex("color", Arr(vertex, Fin(Add(Mul(D(2), m), D(1)))), proper)))));
        }
        else if (declaration == "high_slot_formula_valid")
        {
                var z = V("z");
                var boundary = Fn("i", N, Add(Mul(D(2), i),
                    Card(Call("filter", removed, Fn("t", N, Less(t, i))))));
                var slotColor = Fn("x", vertex, Seq(Langle,
                    Mod(Add(Call("s", Val(Call("fst", x))), Val(Call("snd", x))), c),
                    Rangle, Colon, Fin(c)));
                result = Q("n m a rho", N, Q("k", demandType,
                    Imp(And(bounds, decomposition, Leq(Mul(D(2), rho), a), atMostTwo),
                        Let("c", N, Add(Mul(D(2), m), D(1)),
                            Let("z", N, Mod(Sub(a, Mul(D(2), rho)), c),
                                Let("R", Call("Finset", N), Call("image", Call("range", z),
                                    Fn("q", N, Mul(V("q"), m))),
                                    Let("s", Arr(N, N), boundary,
                                        And(Eqn(Call("s", D(0)), D(0)),
                                            Eqn(Call("s", n), Add(Mul(D(2), n), z)),
                                            Call("Proper", m, k, slotColor)))))))));
        }
        else if (declaration == "high_branch_coloring")
        {
                result = Q("n m a rho", N, Q("k", demandType,
                    Imp(And(bounds, decomposition, Leq(Mul(D(2), rho), a), atMostTwo),
                        Ex("color", Arr(vertex, Fin(Add(Mul(D(2), m), D(1)))), proper))));
        }
        else if (declaration == "cyclicIndex")
        {
                result = Q("n m", N, Imp(Leq(m, n), Q("start", Fin(n), Q("i", Fin(m),
                    Eqn(Val(Call("cyclicIndex", start, i)), Choice(Less(Add(Val(start), Val(i)), n),
                        Add(Val(start), Val(i)), Sub(Add(Val(start), Val(i)), n)))))));
        }
        else if (declaration == "double_window_lower_bound")
        {
                result = Q("n m c", N, Q("k", demandType, Q("start", Fin(n), Q("color", Arr(vertex, Fin(c)),
                    Imp(And(Leq(m, n), Q("i", Fin(m), Eqn(Call("k", Call("cyclicIndex", start, i)), D(2))), proper),
                        Leq(Mul(D(2), m), c))))));
        }
        else if (declaration == "mixed_demand_minimum")
        {
                var L = V("L"); var capacity = V("capacity");
                var feasible = Set("c", N, hasColor);
                var conclusion = Let("L", N, singletonCount,
                    Let("capacity", N, Call("max", Mul(D(2), m), Div(Sub(Add(Sub(Mul(D(2), n), L), a), D(1)), a)),
                        And(Call("IsLeast", feasible, capacity), Eqn(capacity,
                            Add(Mul(D(2), m), Choice(Less(L, Mul(D(2), rho)), D(1), D(0)))))));
                result = Q("n m a rho", N, Q("k", demandType, Q("start", Fin(n),
                    Imp(And(Leq(D(2), m), Less(Mul(D(2), m), n), decomposition, Less(rho, m),
                        Leq(Mul(D(2), rho), a), demands,
                        Q("i", Fin(m), Eqn(Call("k", Call("cyclicIndex", start, i)), D(2)))), conclusion))));
        }
        else
        {
            throw new System.InvalidOperationException("Unknown cyclic statement.");
        }
        return Disp(result);
    }
}
