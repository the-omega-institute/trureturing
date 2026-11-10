using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class LaplacianTwoLevelTreeSpectralBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/coutinho2025peak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On the homogeneous two-level rooted tree T(k, l) of order n = 1 + k(l + 1) with k >= 2 "
        + "hubs and l >= 1 leaves per hub, the continuous-time Laplacian propagator from the root "
        + "to any leaf decomposes across the three eigenvalues 0, a, b of the three-dimensional "
        + "cell-constant invariant subspace. Its distinct-eigenvalue spectral entry bound equals "
        + "2 / (a d), where d = b - a = sqrt((k - l)^2 + 4 l). Scaled by n^(3/2), the squared "
        + "spectral bound is dominated through an algebraic chord identity and rational square "
        + "decompositions by the universal constant C_* = 2 + 6 sqrt(5) / 5, with equality on "
        + "B_{k, l}^2 if and only if (k, l) = (2, 1).",
        H("Sharp global spectral bound for root-to-leaf Laplacian transfer on two-level trees"),
        Blocks(
            Node("tree-order", "treeOrder", "Order of the two-level rooted tree",
                TreeOrderFormula(),
                "For k hubs and l leaves attached to each hub, the total vertex count of T(k, l) "
                + "is n = 1 + k(l + 1), counting the single root together with k hub-and-branch "
                + "blocks of size l + 1.",
                DescribeRole.Definition),
            Node("two-level-tree", "twoLevelTree", "The homogeneous two-level tree on Fin n",
                TwoLevelTreeFormula(),
                "The simple graph T(k, l) on Fin(treeOrder k l) is transported along an explicit "
                + "equivalence from Option(Fin k x Option(Fin l)), where none represents the root, "
                + "some(i, none) represents the i-th hub adjacent to the root, and some(i, some j) "
                + "represents the j-th leaf adjacent to the i-th hub. No edges exist within any "
                + "level or between distinct branches, and twoLevelTreeDecidableRel equips the "
                + "adjacency relation with decidability.",
                DescribeRole.Definition),
            Node("root-vertex", "rootVertex", "The root vertex of T(k, l)",
                RootVertexFormula(),
                "The distinguished root r in Fin(treeOrder k l) corresponds under the vertex "
                + "equivalence to none and has degree k.",
                DescribeRole.Definition),
            Node("hub-vertex", "hubVertex", "The i-th hub vertex of T(k, l)",
                HubVertexFormula(),
                "For i in Fin k, the hub vertex h_i in Fin(treeOrder k l) corresponds to "
                + "some(i, none), is adjacent to the root and to its l leaves, and has degree "
                + "l + 1.",
                DescribeRole.Definition),
            Node("leaf-vertex", "leafVertex", "The (i, j)-th leaf vertex of T(k, l)",
                LeafVertexFormula(),
                "For i in Fin k and j in Fin l, the leaf vertex x_{i, j} in Fin(treeOrder k l) "
                + "corresponds to some(i, some j) and has degree 1 with unique neighbor h_i.",
                DescribeRole.Definition),
            Node("leaf-transfer-prob", "leafTransferProb",
                "Continuous-time Laplacian root-to-leaf transfer probability",
                LeafTransferProbFormula(),
                "At real time t, leafTransferProb k l i j t is the squared complex norm "
                + "|U(t)_{x_{i, j}, r}|^2 of the Laplacian propagator entry "
                + "exp(i t L)_{x_{i, j}, r} from the root r to the leaf x_{i, j}, defined directly "
                + "via LaplacianPeakTransferTrees.lapPropagator on twoLevelTree k l at time t.",
                DescribeRole.Definition),
            Node("leaf-bounding-entry", "leafBoundingEntry",
                "Root-to-leaf entry of the Laplacian spectral bounding matrix",
                LeafBoundingEntryFormula(),
                "Following Section 3 of Coutinho, Guo, and Schmeits (2025), leafBoundingEntry "
                + "k l i j evaluates LaplacianPeakTransferTrees.boundingEntry on twoLevelTree k l "
                + "at the pair (x_{i, j}, r), summing the absolute values of the "
                + "distinct-eigenvalue orthogonal spectral idempotent entries "
                + "|(E_theta)_{x_{i, j}, r}|.",
                DescribeRole.Definition),
            Node("spec-s", "specS", "Trace parameter of the positive root-supported eigenvalues",
                SpecSFormula(),
                "On the three-dimensional subspace of vectors constant on the root, on hubs, and "
                + "on leaves, the nonzero Laplacian eigenvalues satisfy theta^2 - S theta + n = 0 "
                + "with trace parameter S = k + l + 2 over the reals.",
                DescribeRole.Definition),
            Node("spec-d", "specD", "Spectral discriminant parameter",
                SpecDFormula(),
                "The gap between the two positive root-supported eigenvalues is "
                + "d = sqrt((k - l)^2 + 4 l), computed with real subtraction (k : R) - (l : R) "
                + "so that S^2 - 4 n = ((k : R) - (l : R))^2 + 4 l = d^2 holds for all k and l.",
                DescribeRole.Definition),
            Node("spec-a", "specA", "Lower positive root-supported Laplacian eigenvalue",
                SpecAFormula(),
                "The smaller positive root of theta^2 - S theta + n = 0 is a = (S - d) / 2. "
                + "For k >= 2 and l >= 1 one has 1 < a < b and a b = n.",
                DescribeRole.Definition),
            Node("spec-b", "specB", "Upper positive root-supported Laplacian eigenvalue",
                SpecBFormula(),
                "The larger positive root of theta^2 - S theta + n = 0 is b = (S + d) / 2 = a + d.",
                DescribeRole.Definition),
            Node("optimal-const", "optimalTransferConst",
                "Optimal global scaled root-to-leaf transfer constant",
                OptimalTransferConstFormula(),
                "The constant C_* = 2 + 6 sqrt(5) / 5 is the value of the upper-endpoint spectral "
                + "envelope H(d) at the minimal feasible discriminant d = sqrt(5), attained by "
                + "the five-vertex tree T(2, 1).",
                DescribeRole.Definition),
            Node("upper-feasible-a", "upperFeasibleA",
                "Upper feasible endpoint for the lower eigenvalue at fixed discriminant",
                UpperFeasibleAFormula(),
                "At fixed discriminant d, eliminating k and l via 4(A(d) - a) = (k - l - 1)^2 >= 0 "
                + "confines the lower eigenvalue a to the interval [1, A(d)] where "
                + "A(d) = (d^2 - 2 d + 5) / 4.",
                DescribeRole.Definition),
            Node("envelope-g", "envelopeG", "Lower-endpoint spectral envelope",
                EnvelopeGFormula(),
                "Evaluating the scaled squared spectral bound 4(a + d)^(3/2) / (sqrt(a) d^2) at "
                + "the left endpoint a = 1 produces G(d) = 4(d + 1)^(3/2) / d^2.",
                DescribeRole.Definition),
            Node("envelope-h", "envelopeH", "Upper-endpoint spectral envelope",
                EnvelopeHFormula(),
                "Evaluating 4(a + d)^(3/2) / (sqrt(a) d^2) at the right endpoint a = A(d) = "
                + "(d^2 - 2 d + 5) / 4, where a + d = (d^2 + 2 d + 5) / 4, produces "
                + "H(d) = (d^2 + 2 d + 5)^(3/2) / (d^2 sqrt(d^2 - 2 d + 5)).",
                DescribeRole.Definition),
            Node("leaf-dynamics", "twoLevelTree_leaf_dynamics_and_invariance",
                "Exact root-to-leaf spectral decomposition, symmetry invariance, and closed bound",
                LeafDynamicsFormula(),
                "For k >= 2 and l >= 1, the graph T(k, l) is a tree (connected and acyclic) whose "
                + "root has degree k, each hub has degree l + 1, and each leaf has degree 1. "
                + "Swapping branches and permuting leaves within a branch yield graph "
                + "automorphisms fixing the root and mapping any leaf x_{i, j} to any other leaf "
                + "x_{i2, j2}, so both the spectral bounding entry and the transfer probability "
                + "P_{k, l}(t) are independent of the chosen leaf (i, j). Expanding the root "
                + "indicator e_r as (1 / n) v_0 + c_a v_a + c_b v_b in explicit cell-constant "
                + "Laplacian eigenvectors for eigenvalues 0, a, b shows that every other Laplacian "
                + "eigenspace is orthogonal to e_r, yields the three-frequency formula "
                + "U(t)_{x_{i, j}, r} = 1 / n - exp(i a t) / (a d) + exp(i b t) / (b d), "
                + "evaluates the spectral bounding entry to 1 / n + 1 / (a d) + 1 / (b d) = "
                + "2 / (a d) because a b = n and b - a = d, and establishes the universal time "
                + "upper bound P_{k, l}(t) <= B_{k, l}^2.",
                DescribeRole.Theorem),
            Node("envelope-antitonicity", "spectral_envelope_and_antitonicity",
                "Algebraic envelope decompositions, strict antitonicity, and endpoint domination",
                EnvelopeAntitonicityFormula(),
                "For 0 < d_1 < d_2, squaring G(d_1) yields 16(1 / d_1 + 3 / d_1^2 + 3 / d_1^3 + "
                + "1 / d_1^4), and the polynomial identity (d^2 + 2 d + 5)^3 = "
                + "(d^2 - 2 d + 5)(d^4 + 8 d^3 + 38 d^2 + 40 d + 25) + 64 d^3 yields "
                + "H(d_1)^2 = 1 + 8 / d_1 + 38 / d_1^2 + 40 / d_1^3 + 25 / d_1^4 + "
                + "64 / (d_1(d_1^2 - 2 d_1 + 5)). Because d(d^2 - 2 d + 5) = d((d - 1)^2 + 4) is "
                + "positive and strictly increasing on (0, infinity) via the factorization "
                + "d_2(d_2^2 - 2 d_2 + 5) - d_1(d_1^2 - 2 d_1 + 5) = "
                + "(d_2 - d_1)((d_1 - 1)^2 + (d_2 - 1)^2 + d_1 d_2 + 3) > 0, every term of H(d)^2 "
                + "exceeding 1 is positive and strictly decreasing, giving 1 < H(d_1), "
                + "G(d_2) < G(d_1), and H(d_2) < H(d_1). Furthermore, on [1, A(d_1)], the "
                + "function g(a) = (a + d_1)^3 / a satisfies the chord-difference identity "
                + "v a(v - a)(1 + d_1)^3 + a(a - 1)(v + d_1)^3 - v(v - 1)(a + d_1)^3 = "
                + "(v - 1)(a - 1)(v - a)(v a + d_1^3) >= 0 with v = A(d_1), dominating "
                + "4(a + d_1)^(3/2) / (sqrt(a) d_1^2) by max(G(d_1), H(d_1)) without calculus.",
                DescribeRole.Theorem),
            Node("global-bound", "sharp_global_spectral_transfer_bound",
                "Sharp global O(n^(-3/2)) spectral transfer bound and uniqueness of T(2, 1)",
                GlobalBoundFormula(),
                "For every k >= 2, l >= 1, leaf (i, j), and real time t, the spectral parameters "
                + "satisfy d >= sqrt(5), 1 < a <= A(d), and n = a(a + d), so "
                + "n^(3/2) B_{k, l}^2 = 4(a + d)^(3/2) / (sqrt(a) d^2) <= max(G(d), H(d)). "
                + "At d = sqrt(5), direct algebraic evaluation gives H(sqrt(5)) = C_* and "
                + "C_*^2 - G(sqrt(5))^2 = 8(3 - sqrt(5)) / 25 > 0, while strict antitonicity of "
                + "G and H forces max(G(d), H(d)) < C_* whenever d > sqrt(5). Consequently "
                + "P_{k, l}(t) <= B_{k, l}^2 <= C_* n^(-3/2) everywhere, and the scaled spectral "
                + "bound n^(3/2) B_{k, l}^2 attains C_* if and only if d = sqrt(5) and a = A(d), "
                + "which among integers k >= 2 and l >= 1 holds if and only if k = 2 and l = 1.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("ltltsb-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Dotted(string a, string b) => Seq(Named(a), Dot, Named(b));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) =>
        new Formula.Apply(fn, [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula v, Formula t) => Par(Seq(v, Sp, Colon, Sp, t));
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegOf(Formula x) => new Formula.Negate(x);
    private static Formula SqrtOf(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Pow(Formula b, Formula e) =>
        b is Formula.LatexWord ? new Formula.Power(b, e) : new Formula.Power(Par(b), e);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iffn(Formula a, Formula b) =>
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
    private static Formula Some(string v, Formula dom, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), dom, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula ThreeHalves() => FracOf(Num(3), Num(2));
    private static Formula NegThreeHalves() => NegOf(ThreeHalves());

    private static Formula TreeOrderFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l");
        return All("k", Nats(), All("l", Nats(),
            Eqn(Call("treeOrder", k, l), Add(Num(1), Mul(k, Add(l, Num(1)))))));
    }

    private static Formula TwoLevelTreeFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), u = F.Id("u"), v = F.Id("v");
        Formula dom = FinOf(Call("treeOrder", k, l));
        Formula inv = App(Dotted("Equiv", "symm"), Call("vertEquiv", k, l));
        return All("k", Nats(), All("l", Nats(), All("u", dom, All("v", dom,
            Iffn(App(Dotted("SimpleGraph", "Adj"), Call("twoLevelTree", k, l), u, v),
                App(Dotted("SimpleGraph", "Adj"), Call("rawTree", k, l),
                    App(inv, u), App(inv, v)))))));
    }

    private static Formula RootVertexFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l");
        return All("k", Nats(), All("l", Nats(),
            Eqn(Call("rootVertex", k, l), App(Call("vertEquiv", k, l), Named("none")))));
    }

    private static Formula HubVertexFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), i = F.Id("i");
        return All("k", Nats(), All("l", Nats(), All("i", FinOf(k),
            Eqn(Call("hubVertex", k, l, i),
                App(Call("vertEquiv", k, l),
                    Call("some", Par(Seq(i, Comma, Sp, Named("none")))))))));
    }

    private static Formula LeafVertexFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), i = F.Id("i"), j = F.Id("j");
        return All("k", Nats(), All("l", Nats(), All("i", FinOf(k), All("j", FinOf(l),
            Eqn(Call("leafVertex", k, l, i, j),
                App(Call("vertEquiv", k, l),
                    Call("some", Par(Seq(i, Comma, Sp, Call("some", j))))))))));
    }

    private static Formula LeafTransferProbFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), i = F.Id("i"), j = F.Id("j"), t = F.Id("t");
        Formula entry = Call("lapPropagator", Call("twoLevelTree", k, l), t,
            Call("leafVertex", k, l, i, j), Call("rootVertex", k, l));
        return All("k", Nats(), All("l", Nats(), All("i", FinOf(k), All("j", FinOf(l),
            All("t", Reals(), Eqn(Call("leafTransferProb", k, l, i, j, t),
                Pow(new Formula.Norm(entry), Num(2))))))));
    }

    private static Formula LeafBoundingEntryFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), i = F.Id("i"), j = F.Id("j");
        return All("k", Nats(), All("l", Nats(), All("i", FinOf(k), All("j", FinOf(l),
            Eqn(Call("leafBoundingEntry", k, l, i, j),
                Call("boundingEntry", Call("twoLevelTree", k, l),
                    Call("leafVertex", k, l, i, j), Call("rootVertex", k, l)))))));
    }

    private static Formula SpecSFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l");
        return All("k", Nats(), All("l", Nats(),
            Eqn(Call("specS", k, l), Add(Add(Cast(k, Reals()), Cast(l, Reals())), Num(2)))));
    }

    private static Formula SpecDFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l");
        return All("k", Nats(), All("l", Nats(),
            Eqn(Call("specD", k, l),
                SqrtOf(Add(Pow(Sub(Cast(k, Reals()), Cast(l, Reals())), Num(2)),
                    Mul(Num(4), Cast(l, Reals())))))));
    }

    private static Formula SpecAFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l");
        return All("k", Nats(), All("l", Nats(),
            Eqn(Call("specA", k, l),
                FracOf(Sub(Call("specS", k, l), Call("specD", k, l)), Num(2)))));
    }

    private static Formula SpecBFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l");
        return All("k", Nats(), All("l", Nats(),
            Eqn(Call("specB", k, l),
                FracOf(Add(Call("specS", k, l), Call("specD", k, l)), Num(2)))));
    }

    private static Formula OptimalTransferConstFormula() =>
        Eqn(Named("optimalTransferConst"),
            Add(Num(2), FracOf(Mul(Num(6), SqrtOf(Num(5))), Num(5))));

    private static Formula UpperFeasibleAFormula()
    {
        Formula d = F.Id("d");
        return All("d", Reals(),
            Eqn(Call("upperFeasibleA", d),
                FracOf(Add(Sub(Pow(d, Num(2)), Mul(Num(2), d)), Num(5)), Num(4))));
    }

    private static Formula EnvelopeGFormula()
    {
        Formula d = F.Id("d");
        return All("d", Reals(),
            Eqn(Call("envelopeG", d),
                FracOf(Mul(Num(4), Pow(Add(d, Num(1)), ThreeHalves())), Pow(d, Num(2)))));
    }

    private static Formula EnvelopeHFormula()
    {
        Formula d = F.Id("d");
        Formula qp = Add(Add(Pow(d, Num(2)), Mul(Num(2), d)), Num(5));
        Formula qm = Add(Sub(Pow(d, Num(2)), Mul(Num(2), d)), Num(5));
        return All("d", Reals(),
            Eqn(Call("envelopeH", d),
                FracOf(Pow(qp, ThreeHalves()), Mul(Pow(d, Num(2)), SqrtOf(qm)))));
    }

    private static Formula LeafDynamicsFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), t = F.Id("t"), phi = F.Id("phi");
        Formula i = F.Id("i"), i2 = F.Id("i2"), j = F.Id("j"), j2 = F.Id("j2");
        Formula g = Call("twoLevelTree", k, l), r = Call("rootVertex", k, l);
        Formula nC = Cast(Call("treeOrder", k, l), Complexes());
        Formula aC = Cast(Call("specA", k, l), Complexes());
        Formula bC = Cast(Call("specB", k, l), Complexes());
        Formula dC = Cast(Call("specD", k, l), Complexes()), tC = Cast(t, Complexes());
        Formula im = Dotted("Complex", "I"), cexp = Dotted("Complex", "exp");
        Formula propRhs = Add(Sub(FracOf(Cast(Num(1), Complexes()), nC),
                FracOf(App(cexp, Mul(Mul(im, aC), tC)), Mul(aC, dC))),
            FracOf(App(cexp, Mul(Mul(im, bC), tC)), Mul(bC, dC)));
        Formula aut = Some("phi", App(Dotted("SimpleGraph", "Iso"), g, g),
            AndAll(Eqn(App(phi, r), r),
                Eqn(App(phi, Call("leafVertex", k, l, i, j)),
                    Call("leafVertex", k, l, i2, j2))));
        Formula concl = AndAll(
            App(Dotted("SimpleGraph", "IsTree"), g), aut,
            Eqn(Call("leafTransferProb", k, l, i, j, t),
                Call("leafTransferProb", k, l, i2, j2, t)),
            Eqn(Call("leafBoundingEntry", k, l, i, j),
                Call("leafBoundingEntry", k, l, i2, j2)),
            Eqn(Call("lapPropagator", g, t, Call("leafVertex", k, l, i, j), r), propRhs),
            Eqn(Call("leafBoundingEntry", k, l, i, j),
                FracOf(Num(2), Mul(Call("specA", k, l), Call("specD", k, l)))),
            LeOf(Call("leafTransferProb", k, l, i, j, t),
                Pow(Call("leafBoundingEntry", k, l, i, j), Num(2))));
        return All("k", Nats(), All("l", Nats(),
            Imp(LeOf(Num(2), k), Imp(LeOf(Num(1), l),
                All("i", FinOf(k), All("i2", FinOf(k),
                    All("j", FinOf(l), All("j2", FinOf(l), All("t", Reals(), concl)))))))));
    }

    private static Formula EnvelopeAntitonicityFormula()
    {
        Formula d1 = F.Id("d1"), d2 = F.Id("d2"), a = F.Id("a");
        Formula gSq = Eqn(Pow(Call("envelopeG", d1), Num(2)),
            Mul(Num(16), Add(Add(Add(FracOf(Num(1), d1), FracOf(Num(3), Pow(d1, Num(2)))),
                FracOf(Num(3), Pow(d1, Num(3)))), FracOf(Num(1), Pow(d1, Num(4))))));
        Formula hSq = Eqn(Pow(Call("envelopeH", d1), Num(2)),
            Add(Add(Add(Add(Add(Num(1), FracOf(Num(8), d1)),
                        FracOf(Num(38), Pow(d1, Num(2)))),
                    FracOf(Num(40), Pow(d1, Num(3)))),
                FracOf(Num(25), Pow(d1, Num(4)))),
                FracOf(Num(64), Mul(d1, Add(Sub(Pow(d1, Num(2)), Mul(Num(2), d1)), Num(5))))));
        Formula chord = All("a", Reals(), Imp(LeOf(Num(1), a),
            Imp(LeOf(a, Call("upperFeasibleA", d1)),
                LeOf(FracOf(Mul(Num(4), Pow(Add(a, d1), ThreeHalves())),
                        Mul(SqrtOf(a), Pow(d1, Num(2)))),
                    Call("max", Call("envelopeG", d1), Call("envelopeH", d1))))));
        return All("d1", Reals(), All("d2", Reals(),
            Imp(LtOf(Num(0), d1), Imp(LtOf(d1, d2),
                AndAll(gSq, hSq, LtOf(Num(1), Call("envelopeH", d1)),
                    LtOf(Call("envelopeG", d2), Call("envelopeG", d1)),
                    LtOf(Call("envelopeH", d2), Call("envelopeH", d1)), chord)))));
    }

    private static Formula GlobalBoundFormula()
    {
        Formula k = F.Id("k"), l = F.Id("l"), i = F.Id("i"), j = F.Id("j"), t = F.Id("t");
        Formula nR = Cast(Call("treeOrder", k, l), Reals());
        Formula d = Call("specD", k, l), a = Call("specA", k, l);
        Formula bndSq = Pow(Call("leafBoundingEntry", k, l, i, j), Num(2));
        Formula scaled = Mul(Pow(nR, ThreeHalves()), bndSq);
        Formula concl = AndAll(
            LeOf(SqrtOf(Num(5)), d), LtOf(Num(1), a), LeOf(a, Call("upperFeasibleA", d)),
            Eqn(nR, Mul(a, Add(a, d))),
            LeOf(scaled, Call("max", Call("envelopeG", d), Call("envelopeH", d))),
            LeOf(Call("leafTransferProb", k, l, i, j, t), bndSq),
            LeOf(bndSq, Mul(Named("optimalTransferConst"), Pow(nR, NegThreeHalves()))),
            Iffn(Eqn(scaled, Named("optimalTransferConst")),
                AndAll(Eqn(k, Num(2)), Eqn(l, Num(1)))));
        return All("k", Nats(), All("l", Nats(),
            Imp(LeOf(Num(2), k), Imp(LeOf(Num(1), l),
                All("i", FinOf(k), All("j", FinOf(l), All("t", Reals(), concl)))))));
    }
}
