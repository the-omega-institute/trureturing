using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class UnequalSpiderPowerZeroForcingDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/abiadflaggghaseminezhadzeijlemaker2026powers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For integers m >= 2 and k >= 1 and independently chosen leg lengths "
        + "ell_0, ..., ell_{m - 1} >= k + 1, the ordinary distance-at-most-k power G = T^k of the "
        + "spider T on N = 1 + sum_{i = 0}^{m - 1} ell_i vertices has ordinary zero forcing "
        + "number Z(G) = (m - 1) k, real symmetric maximum nullity M_R(G) = (m - 1) k, and real "
        + "symmetric minimum rank mr_R(G) = N - (m - 1) k. The upper bound Z(G) <= (m - 1) k is "
        + "realized by the tail set consisting of the last k vertices on each of the first m - 1 "
        + "legs, while the matching lower bound and symmetric extremum are realized by one "
        + "explicit real symmetric matrix combining per-leg sliding-window Gram blocks "
        + "D_{ell_i}^T D_{ell_i} with cross-leg and center indicator couplings.",
        H("Ordinary zero forcing, symmetric maximum nullity, and minimum rank of unequal-leg spider powers"),
        Blocks(
            DefNode("vertex", "Vertex",
                "Vertex type of a spider with independently chosen leg lengths",
                VertexFormula(),
                "For m : Nat and leg-length profile ell : Fin m -> Nat, Vertex m ell is "
                + "Option (Sigma i : Fin m, Fin (ell i)). The constructor none denotes the center "
                + "vertex c, while some <i, d> denotes the vertex on 1-based leg i_1 = i.val + 1 "
                + "(1 <= i_1 <= m) at 1-based depth d_1 = d.val + 1 (1 <= d_1 <= ell i) from the "
                + "center."),
            DefNode("spider-tree", "spiderTree",
                "Spider tree on independently varying leg lengths",
                SpiderTreeFormula(),
                "The simple graph spiderTree m ell joins the center none to some <i, d> precisely "
                + "when d.val = 0 (1-based depth 1), and joins two leg vertices some <i, d> and "
                + "some <j, e> precisely when i = j and Nat.dist d.val e.val = 1."),
            DefNode("distance", "distance",
                "Closed-form spider-tree distance",
                DistanceFormula(),
                "The function distance m ell evaluates to 0 at (none, none), to d.val + 1 between "
                + "none and some <i, d> (matching 1-based depth d_1 = d.val + 1), to "
                + "Nat.dist d.val e.val = |d_1 - e_1| for two vertices on the same leg i = j, and "
                + "to d.val + e.val + 2 = d_1 + e_1 for two vertices on distinct legs i != j."),
            DefNode("power", "power",
                "Ordinary distance-at-most-k spider power",
                PowerFormula(),
                "The simple graph power m k ell on Vertex m ell joins distinct vertices u != v "
                + "precisely when distance m ell u v <= k."),
            DefNode("sym-graph-matrices", "SymGraphMatrices",
                "Real symmetric matrix family of a simple graph",
                SymGraphMatricesFormula(),
                "For a simple graph G on V : Type, SymGraphMatrices G is the set of real matrices "
                + "A : Matrix V V R that are symmetric (A.IsSymm) and satisfy A u v != 0 <-> "
                + "G.Adj u v for all distinct vertices u != v, with diagonal entries "
                + "unconstrained."),
            DefNode("matrix-nullity", "matrixNullity",
                "Right-kernel dimension of a real square matrix",
                MatrixNullityFormula(),
                "For a finite vertex type V and matrix A : Matrix V V R, matrixNullity A is "
                + "Module.finrank R (LinearMap.ker A.mulVecLin)."),
            DefNode("max-sym-nullity", "maxSymNullity",
                "Maximum symmetric nullity of a finite simple graph",
                MaxSymNullityFormula(),
                "For a simple graph G on a finite vertex type V, maxSymNullity G is the supremum "
                + "sSup (matrixNullity '' SymGraphMatrices G) in Nat."),
            DefNode("min-sym-rank", "minSymRank",
                "Minimum symmetric rank of a finite simple graph",
                MinSymRankFormula(),
                "For a simple graph G on a finite vertex type V, minSymRank G is the infimum "
                + "sInf (Matrix.rank '' SymGraphMatrices G) in Nat."),
            DefNode("sliding-window-space", "slidingWindowSpace",
                "One-sided (k + 1)-term zero-sum sliding-window subspace",
                SlidingWindowSpaceFormula(),
                "For k : Nat, slidingWindowSpace k is the R-submodule of sequences x : Nat -> R "
                + "such that sum_{t in Finset.range (k + 1)} x(s + t) = 0 for every start index "
                + "s : Nat."),
            DefNode("sliding-window-equiv", "slidingWindowEquiv",
                "Initial-coordinate linear equivalence on the sliding-window subspace",
                SlidingWindowEquivFormula(),
                "For k : Nat, slidingWindowEquiv k : slidingWindowSpace k ≃_l[R] (Fin k -> R) "
                + "evaluates a sequence x on its first k coordinates i |-> x.1 i.val, with "
                + "explicit (k + 1)-periodic inverse sending v : Fin k -> R at index n : Nat to "
                + "v (n mod (k + 1)) when n mod (k + 1) < k and to -sum_{i : Fin k} v i when "
                + "n mod (k + 1) = k."),
            DefNode("window-matrix", "windowMatrix",
                "Rectangular sliding-window indicator matrix",
                WindowMatrixFormula(),
                "For k, L : Nat, windowMatrix k L is the (L - k) x L real matrix D_L whose entry "
                + "at row s : Fin (L - k) and column d : Fin L equals 1 when "
                + "s.val <= d.val <= s.val + k and 0 otherwise."),
            DefNode("spider-tail-forcing-set", "spiderTailForcingSet",
                "Tail zero-forcing set on the first m - 1 legs",
                SpiderTailForcingSetFormula(),
                "For m, k : Nat and leg-length profile ell : Fin m -> Nat, spiderTailForcingSet "
                + "m k ell collects the leg vertices some <i, d> with i.val < m - 1 (the first "
                + "m - 1 legs) and ell i - k <= d.val (the last k depths on leg i)."),
            DefNode("center-coupling", "centerCoupling",
                "Center-to-leg coupling entry",
                CenterCouplingFormula(),
                "For k, d : Nat, centerCoupling k d equals 1 when d + 1 <= k (so 1-based depth "
                + "d_1 = d + 1 lies within distance k of the center) and 0 otherwise."),
            DefNode("cross-coupling", "crossCoupling",
                "Cross-leg coupling entry",
                CrossCouplingFormula(),
                "For k, d, e : Nat, crossCoupling k d e equals 1 when d + 1 <= k - 1, "
                + "e + 1 <= k - 1, and (d + 1) + (e + 1) <= k (equivalently d + e + 2 <= k, "
                + "matching 1-based cross-leg distance d_1 + e_1 <= k) and 0 otherwise."),
            DefNode("spider-symm-matrix", "spiderSymmMatrix",
                "Explicit extremal real symmetric matrix for an unequal-leg spider power",
                SpiderSymmMatrixFormula(),
                "On Vertex m ell, spiderSymmMatrix m k ell places 0 at (none, none), "
                + "centerCoupling k p.2.val between none and any leg vertex some p, "
                + "crossCoupling k p.2.val q.2.val between vertices on distinct legs, and "
                + "(D_{ell_i}^T D_{ell_i})_{d, e} + crossCoupling k d.val e.val between vertices "
                + "at 0-based depths d, e on the same leg i, where D_{ell_i} = windowMatrix k "
                + "(ell i)."),
            AuthorThmNode("sliding-window-kernel-and-band-support",
                "sliding_window_kernel_and_band_support",
                "Recurrence, dimension, truncation annihilation, and Gram band support of sliding windows",
                SlidingWindowTheoremFormula(),
                "Every sequence x : Nat -> R belongs to slidingWindowSpace k if and only if it "
                + "satisfies the order-k recurrence x(s + k) = -sum_{t < k} x(s + t) for all "
                + "s : Nat. Consequently, initial-coordinate evaluation slidingWindowEquiv k "
                + "establishes unique extension from Fin k -> R and gives Module.finrank R "
                + "(slidingWindowSpace k) = k for every k : Nat (including k = 0). Whenever "
                + "L >= k + 1, truncating any x in slidingWindowSpace k to Fin L lies in the "
                + "right kernel of windowMatrix k L, while for all distinct d, e : Fin L the Gram "
                + "entry ((windowMatrix k L)^T * windowMatrix k L) d e is strictly positive if "
                + "and only if Nat.dist d.val e.val <= k, realized when Nat.dist d.val e.val <= k "
                + "by the window start s_0 = max(d.val, e.val) - k < L - k."),
            AuthorThmNode("unequal-spider-power-zero-forcing",
                "unequal_spider_power_zero_forcing",
                "Zero forcing number, maximum symmetric nullity, and minimum symmetric rank of unequal-leg spider powers",
                UnequalSpiderTheoremFormula(),
                "Assume m >= 2, k >= 1, and ell i >= k + 1 for every i : Fin m. Then Vertex m ell "
                + "has cardinality N = 1 + sum_i ell i, the graph metric (spiderTree m ell).dist "
                + "equals distance m ell everywhere, and adjacency in power m k ell coincides "
                + "with distinctness and spider-tree distance at most k. The tail set "
                + "spiderTailForcingSet m k ell has cardinality (m - 1) k and zero-forces "
                + "power m k ell in four phases: inward along each of the first m - 1 legs, from "
                + "0-based depth k - 1 on leg 0 to the center, from depths k - t - 2 on leg 0 to "
                + "depths t < k - 1 on leg m - 1, from the center to depth k - 1 on leg m - 1, "
                + "and outward along leg m - 1. Conversely, spiderSymmMatrix m k ell belongs to "
                + "SymGraphMatrices (power m k ell) because nonnegativity of crossCoupling and "
                + "the Gram band support of windowMatrix k (ell i) match same-leg adjacency while "
                + "crossCoupling and centerCoupling match cross-leg and center adjacency. "
                + "Assigning arbitrary sequences from slidingWindowSpace k to the first m - 1 "
                + "legs and their negative sum to leg m - 1 embeds (Fin (m - 1) x Fin k -> R) "
                + "injectively into ker(spiderSymmMatrix m k ell), giving nullity >= (m - 1) k. "
                + "For every H in SymGraphMatrices (power m k ell) and every finite zero-forcing "
                + "set S, induction along Black shows that any kernel vector of H vanishing on S "
                + "vanishes on all of Vertex m ell, so matrixNullity H <= S.card. Combining both "
                + "inequalities with rank-nullity yields matrixNullity (spiderSymmMatrix m k ell) "
                + "= (m - 1) k, (spiderSymmMatrix m k ell).rank = N - (m - 1) k, the universal "
                + "bounds and extremal characterizations IsGreatest and IsLeast across "
                + "SymGraphMatrices (power m k ell), and the exact invariants "
                + "zeroForcingNumber (power m k ell) = maxSymNullity (power m k ell) = (m - 1) k "
                + "and minSymRank (power m k ell) = N - (m - 1) k.")),
        []));

    private static DocumentBlock DefNode(string id, string name, string title, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("uspzf-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock AuthorThmNode(string id, string name, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create("uspzf-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Dotted(string a, string b) => Seq(Named(a), Dot, Named(b));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) =>
        new Formula.Apply(fn, [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula v, Formula t) => Par(Seq(v, Sp, Colon, Sp, t));
    private static Formula FuncType(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula NegOf(Formula x) => new Formula.Negate(x);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NeqOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula MemOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula AndAll(params Formula[] items)
    {
        var acc = items[^1];
        for (var idx = items.Length - 2; idx >= 0; idx--)
            acc = new Formula.Logic(Par(items[idx]), FormulaLogicOperator.And, Par(acc));
        return acc;
    }
    private static Formula All(string v, Formula dom, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), dom, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula k) => Call("Fin", k);
    private static Formula ValOf(Formula x) => Seq(x, Dot, Named("val"));
    private static Formula FstOf(Formula x) => Seq(x, Dot, Num(1));
    private static Formula SndOf(Formula x) => Seq(x, Dot, Num(2));
    private static Formula AnglePair(Formula a, Formula b) =>
        Seq(Langle, Sp, a, Comma, Sp, b, Sp, Rangle);
    private static Formula Ite(Formula cond, Formula t, Formula e) =>
        Seq(Named("if"), Sp, cond, Sp, Named("then"), Sp, t, Sp, Named("else"), Sp, e);
    private static Formula Dite(string h, Formula cond, Formula t, Formula e) =>
        Seq(Named("if"), Sp, F.Id(h), Sp, Colon, Sp, cond, Sp, Named("then"), Sp, t,
            Sp, Named("else"), Sp, e);
    private static Formula TransposeOf(Formula mat) =>
        Seq(Par(mat), Caret, Grp(Seq(Mathrm, Grp(F.Id("T")))));
    private static Formula MulVecOf(Formula mat, Formula vec) =>
        Seq(Par(mat), Sp, Star, Underscore, Grp(F.Id("v")), Sp, Par(vec));
    private static Formula ImageOf(Formula fn, Formula set) =>
        Seq(fn, Sp, Apos, Apos, Sp, set);
    private static Formula SumRange(string idx, Formula upper, Formula summand) =>
        Seq(Sum, Underscore,
            Grp(Seq(F.Id(idx), Sp, InMacro, Sp, App(Dotted("Finset", "range"), upper))),
            Sp, summand);
    private static Formula SumType(string idx, Formula dom, Formula summand) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(idx), Sp, Colon, Sp, dom)), Sp, summand);
    private static Formula SigmaLegType(Formula m, Formula ell) =>
        Par(Seq(Sigma, Sp, Cast(F.Id("i"), FinOf(m)), Comma, Sp, FinOf(App(ell, F.Id("i")))));
    private static Formula FiniteCarrier(Formula body) =>
        All("V", Named("Type"),
            Seq(OpenBracket, Call("Fintype", F.Id("V")), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", F.Id("V")), CloseBracket, Sp, body));

    private static Formula VertexFormula()
    {
        Formula m = F.Id("m"), ell = F.Id("ell");
        return All("m", Nats(), All("ell", FuncType(FinOf(m), Nats()),
            Eqn(Call("Vertex", m, ell),
                Call("Option", SigmaLegType(m, ell)))));
    }

    private static Formula SpiderTreeFormula()
    {
        Formula m = F.Id("m"), ell = F.Id("ell"), p = F.Id("p"), q = F.Id("q");
        Formula leg = SigmaLegType(m, ell);
        Formula g = Call("spiderTree", m, ell);
        Formula adjFn = Seq(Par(g), Dot, Named("Adj"));
        return All("m", Nats(), All("ell", FuncType(FinOf(m), Nats()), AndAll(
            IffOf(App(adjFn, Named("none"), Named("none")), Named("False")),
            All("p", leg, IffOf(App(adjFn, Named("none"), Call("some", p)),
                Eqn(ValOf(SndOf(p)), Num(0)))),
            All("p", leg, IffOf(App(adjFn, Call("some", p), Named("none")),
                Eqn(ValOf(SndOf(p)), Num(0)))),
            All("p", leg, All("q", leg,
                IffOf(App(adjFn, Call("some", p), Call("some", q)),
                    AndAll(Eqn(FstOf(p), FstOf(q)),
                        Eqn(App(Dotted("Nat", "dist"), ValOf(SndOf(p)), ValOf(SndOf(q))),
                            Num(1)))))))));
    }

    private static Formula DistanceFormula()
    {
        Formula m = F.Id("m"), ell = F.Id("ell"), p = F.Id("p"), q = F.Id("q");
        Formula leg = SigmaLegType(m, ell);
        return All("m", Nats(), All("ell", FuncType(FinOf(m), Nats()), AndAll(
            Eqn(Call("distance", m, ell, Named("none"), Named("none")), Num(0)),
            All("p", leg, Eqn(Call("distance", m, ell, Named("none"), Call("some", p)),
                Add(ValOf(SndOf(p)), Num(1)))),
            All("p", leg, Eqn(Call("distance", m, ell, Call("some", p), Named("none")),
                Add(ValOf(SndOf(p)), Num(1)))),
            All("p", leg, All("q", leg,
                Eqn(Call("distance", m, ell, Call("some", p), Call("some", q)),
                    Ite(Eqn(FstOf(p), FstOf(q)),
                        App(Dotted("Nat", "dist"), ValOf(SndOf(p)), ValOf(SndOf(q))),
                        Add(Add(ValOf(SndOf(p)), ValOf(SndOf(q))), Num(2)))))))));
    }

    private static Formula PowerFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), ell = F.Id("ell"), u = F.Id("u"), v = F.Id("v");
        Formula vert = Call("Vertex", m, ell);
        Formula adjFn = Seq(Par(Call("power", m, k, ell)), Dot, Named("Adj"));
        return All("m", Nats(), All("k", Nats(), All("ell", FuncType(FinOf(m), Nats()),
            All("u", vert, All("v", vert,
                IffOf(App(adjFn, u, v),
                    AndAll(NeqOf(u, v), LeOf(Call("distance", m, ell, u, v), k))))))));
    }

    private static Formula SymGraphMatricesFormula()
    {
        Formula vType = F.Id("V"), g = F.Id("G"), a = F.Id("A"), u = F.Id("u"), v = F.Id("v");
        Formula matType = Call("Matrix", vType, vType, Reals());
        Formula pred = AndAll(
            Seq(a, Dot, Named("IsSymm")),
            All("u", vType, All("v", vType,
                Imp(NeqOf(u, v),
                    IffOf(NeqOf(App(a, u, v), Num(0)),
                        App(Seq(g, Dot, Named("Adj")), u, v))))));
        return All("V", Named("Type"), All("G", Call("SimpleGraph", vType),
            Eqn(Call("SymGraphMatrices", g),
                Seq(OpenBrace, a, Sp, Colon, Sp, matType, Sp, Bar, Sp, pred, CloseBrace))));
    }

    private static Formula MatrixNullityFormula()
    {
        Formula vType = F.Id("V"), a = F.Id("A");
        return FiniteCarrier(All("A", Call("Matrix", vType, vType, Reals()),
            Eqn(Call("matrixNullity", a),
                App(Dotted("Module", "finrank"), Reals(),
                    App(Dotted("LinearMap", "ker"), Seq(a, Dot, Named("mulVecLin")))))));
    }

    private static Formula MaxSymNullityFormula()
    {
        Formula vType = F.Id("V"), g = F.Id("G");
        return FiniteCarrier(All("G", Call("SimpleGraph", vType),
            Eqn(Call("maxSymNullity", g),
                Call("sSup", ImageOf(Named("matrixNullity"), Call("SymGraphMatrices", g))))));
    }

    private static Formula MinSymRankFormula()
    {
        Formula vType = F.Id("V"), g = F.Id("G");
        return FiniteCarrier(All("G", Call("SimpleGraph", vType),
            Eqn(Call("minSymRank", g),
                Call("sInf", ImageOf(Dotted("Matrix", "rank"), Call("SymGraphMatrices", g))))));
    }

    private static Formula SlidingWindowSpaceFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x"), s = F.Id("s"), t = F.Id("t");
        return All("k", Nats(), All("x", FuncType(Nats(), Reals()),
            IffOf(MemOf(x, Call("slidingWindowSpace", k)),
                All("s", Nats(),
                    Eqn(SumRange("t", Add(k, Num(1)), App(x, Add(s, t))), Num(0))))));
    }

    private static Formula SlidingWindowEquivFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x"), i = F.Id("i"), v = F.Id("v"), n = F.Id("n");
        Formula modExpr = new Formula.Modulo(n, Add(k, Num(1)));
        Formula fwd = All("x", Call("slidingWindowSpace", k), All("i", FinOf(k),
            Eqn(Call("slidingWindowEquiv", k, x, i), App(FstOf(x), ValOf(i)))));
        Formula invLhs = App(FstOf(App(Seq(Par(Call("slidingWindowEquiv", k)), Dot, Named("symm")),
            v)), n);
        Formula invRhs = Dite("h", LtOf(modExpr, k),
            App(v, AnglePair(modExpr, F.Id("h"))),
            NegOf(SumType("i", FinOf(k), App(v, i))));
        Formula inv = All("v", FuncType(FinOf(k), Reals()), All("n", Nats(),
            Eqn(invLhs, invRhs)));
        return All("k", Nats(), AndAll(fwd, inv));
    }

    private static Formula WindowMatrixFormula()
    {
        Formula k = F.Id("k"), l = F.Id("L"), s = F.Id("s"), d = F.Id("d");
        return All("k", Nats(), All("L", Nats(),
            All("s", FinOf(Sub(l, k)), All("d", FinOf(l),
                Eqn(Call("windowMatrix", k, l, s, d),
                    Ite(AndAll(LeOf(ValOf(s), ValOf(d)), LeOf(ValOf(d), Add(ValOf(s), k))),
                        Num(1), Num(0)))))));
    }

    private static Formula SpiderTailForcingSetFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), ell = F.Id("ell"), i = F.Id("i"), d = F.Id("d");
        Formula univ = Dotted("Finset", "univ");
        Formula legs = Seq(Par(univ), Dot, Named("filter"), Sp,
            Par(Seq(Named("fun"), Sp, Cast(i, FinOf(m)), Sp, Mapsto, Sp,
                LtOf(ValOf(i), Sub(m, Num(1))))));
        Formula depths = Seq(Named("fun"), Sp, i, Sp, Mapsto, Sp,
            Par(univ), Dot, Named("filter"), Sp,
            Par(Seq(Named("fun"), Sp, Cast(d, FinOf(App(ell, i))), Sp, Mapsto, Sp,
                LeOf(Sub(App(ell, i), k), ValOf(d)))));
        Formula sigmaSet = Seq(Par(legs), Dot, Named("sigma"), Sp, Par(depths));
        Formula someInj = Seq(Named("Option"), Dot, Named("some"), Underscore,
            Grp(Named("injective")));
        Formula emb = AnglePair(Dotted("Option", "some"),
            Seq(someInj, Sp, SigmaLegType(m, ell)));
        return All("m", Nats(), All("k", Nats(), All("ell", FuncType(FinOf(m), Nats()),
            Eqn(Call("spiderTailForcingSet", m, k, ell),
                Seq(Par(sigmaSet), Dot, Named("map"), Sp, emb)))));
    }

    private static Formula CenterCouplingFormula()
    {
        Formula k = F.Id("k"), d = F.Id("d");
        return All("k", Nats(), All("d", Nats(),
            Eqn(Call("centerCoupling", k, d),
                Ite(LeOf(Add(d, Num(1)), k), Num(1), Num(0)))));
    }

    private static Formula CrossCouplingFormula()
    {
        Formula k = F.Id("k"), d = F.Id("d"), e = F.Id("e");
        Formula cond = AndAll(
            LeOf(Add(d, Num(1)), Sub(k, Num(1))),
            LeOf(Add(e, Num(1)), Sub(k, Num(1))),
            LeOf(Add(Add(d, Num(1)), Add(e, Num(1))), k));
        return All("k", Nats(), All("d", Nats(), All("e", Nats(),
            Eqn(Call("crossCoupling", k, d, e), Ite(cond, Num(1), Num(0))))));
    }

    private static Formula SpiderSymmMatrixFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), ell = F.Id("ell"), p = F.Id("p"), q = F.Id("q");
        Formula leg = SigmaLegType(m, ell);
        Formula wm = Call("windowMatrix", k, App(ell, FstOf(p)));
        Formula gram = Mul(TransposeOf(wm), wm);
        Formula castQ = App(Dotted("Fin", "cast"),
            Call("congrArg", ell, Seq(F.Id("h"), Dot, Named("symm"))), SndOf(q));
        Formula sameTerm = Dite("h", Eqn(FstOf(p), FstOf(q)),
            App(Par(gram), SndOf(p), castQ), Num(0));
        return All("m", Nats(), All("k", Nats(), All("ell", FuncType(FinOf(m), Nats()), AndAll(
            Eqn(Call("spiderSymmMatrix", m, k, ell, Named("none"), Named("none")), Num(0)),
            All("p", leg, Eqn(Call("spiderSymmMatrix", m, k, ell, Named("none"), Call("some", p)),
                Call("centerCoupling", k, ValOf(SndOf(p))))),
            All("p", leg, Eqn(Call("spiderSymmMatrix", m, k, ell, Call("some", p), Named("none")),
                Call("centerCoupling", k, ValOf(SndOf(p))))),
            All("p", leg, All("q", leg,
                Eqn(Call("spiderSymmMatrix", m, k, ell, Call("some", p), Call("some", q)),
                    Add(Par(sameTerm),
                        Call("crossCoupling", k, ValOf(SndOf(p)), ValOf(SndOf(q)))))))))));
    }

    private static Formula SlidingWindowTheoremFormula()
    {
        Formula k = F.Id("k"), x = F.Id("x"), s = F.Id("s"), t = F.Id("t"), i = F.Id("i"),
            v = F.Id("v"), l = F.Id("L"), d = F.Id("d"), e = F.Id("e");
        Formula natReal = FuncType(Nats(), Reals());
        Formula space = Call("slidingWindowSpace", k);
        Formula c1 = All("x", natReal,
            IffOf(MemOf(x, space),
                All("s", Nats(),
                    Eqn(App(x, Add(s, k)),
                        NegOf(SumRange("t", k, App(x, Add(s, t))))))));
        Formula c2 = All("x", space, All("i", FinOf(k),
            Eqn(Call("slidingWindowEquiv", k, x, i), App(FstOf(x), ValOf(i)))));
        Formula c3 = All("v", FuncType(FinOf(k), Reals()),
            Seq(Exists, Bang, Sp, Cast(x, natReal), Comma, Sp,
                AndAll(MemOf(x, space),
                    All("i", FinOf(k), Eqn(App(x, ValOf(i)), App(v, i))))));
        Formula c4 = Eqn(App(Dotted("Module", "finrank"), Reals(), space), k);
        Formula truncVec = Seq(Named("fun"), Sp, Cast(d, FinOf(l)), Sp, Mapsto, Sp,
            App(x, ValOf(d)));
        Formula c5 = All("L", Nats(), Imp(LeOf(Add(k, Num(1)), l),
            All("x", natReal, Imp(MemOf(x, space),
                Eqn(MulVecOf(Call("windowMatrix", k, l), truncVec), Num(0))))));
        Formula wm = Call("windowMatrix", k, l);
        Formula gramEntry = App(Par(Mul(TransposeOf(wm), wm)), d, e);
        Formula c6 = All("L", Nats(), Imp(LeOf(Add(k, Num(1)), l),
            All("d", FinOf(l), All("e", FinOf(l), Imp(NeqOf(d, e),
                IffOf(LtOf(Num(0), gramEntry),
                    LeOf(App(Dotted("Nat", "dist"), ValOf(d), ValOf(e)), k)))))));
        return All("k", Nats(), AndAll(c1, c2, c3, c4, c5, c6));
    }

    private static Formula UnequalSpiderTheoremFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), ell = F.Id("ell"), i = F.Id("i"),
            u = F.Id("u"), v = F.Id("v"), hMat = F.Id("H");
        Formula vert = Call("Vertex", m, ell);
        Formula tree = Call("spiderTree", m, ell);
        Formula gPow = Call("power", m, k, ell);
        Formula tailSet = Call("spiderTailForcingSet", m, k, ell);
        Formula symSet = Call("SymGraphMatrices", gPow);
        Formula symMat = Call("spiderSymmMatrix", m, k, ell);
        Formula qVal = Mul(Par(Sub(m, Num(1))), k);
        Formula nVal = Add(Num(1), SumType("i", FinOf(m), App(ell, i)));
        Formula rVal = Sub(Par(nVal), qVal);

        Formula d1 = Eqn(App(Dotted("Fintype", "card"), vert), nVal);
        Formula d2 = All("u", vert, All("v", vert,
            Eqn(App(Seq(Par(tree), Dot, Named("dist")), u, v),
                Call("distance", m, ell, u, v))));
        Formula d3 = All("u", vert, All("v", vert,
            IffOf(App(Seq(Par(gPow), Dot, Named("Adj")), u, v),
                AndAll(NeqOf(u, v),
                    LeOf(App(Seq(Par(tree), Dot, Named("dist")), u, v), k)))));
        Formula d4 = Call("IsZeroForcing", gPow, Cast(tailSet, Call("Set", vert)));
        Formula d5 = Eqn(Seq(Par(tailSet), Dot, Named("card")), qVal);
        Formula d6 = MemOf(symMat, symSet);
        Formula d7 = Eqn(Call("matrixNullity", symMat), qVal);
        Formula d8 = Eqn(Seq(Par(symMat), Dot, Named("rank")), rVal);
        Formula d9 = All("H", Call("Matrix", vert, vert, Reals()),
            Imp(MemOf(hMat, symSet),
                AndAll(LeOf(Call("matrixNullity", hMat), qVal),
                    LeOf(rVal, Seq(hMat, Dot, Named("rank"))))));
        Formula d10 = Call("IsGreatest", ImageOf(Named("matrixNullity"), symSet), qVal);
        Formula d11 = Call("IsLeast", ImageOf(Dotted("Matrix", "rank"), symSet), rVal);
        Formula d12 = Eqn(Call("zeroForcingNumber", gPow), qVal);
        Formula d13 = Eqn(Call("maxSymNullity", gPow), qVal);
        Formula d14 = Eqn(Call("minSymRank", gPow), rVal);

        Formula hell = All("i", FinOf(m), LeOf(Add(k, Num(1)), App(ell, i)));
        return All("m", Nats(), All("k", Nats(), All("ell", FuncType(FinOf(m), Nats()),
            Imp(LeOf(Num(2), m), Imp(LeOf(Num(1), k), Imp(hell,
                AndAll(d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14)))))));
    }
}
