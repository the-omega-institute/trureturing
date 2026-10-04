using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class DissipativeFreeFermionRootLocationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fukaiyoshidakatsura2026dissipative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite claw-free, even-hole-free graph with a simplicial clique, real couplings, a positive dissipation rate and no common root of the two independence polynomials, every root of the dissipative polynomial lies in the open upper half-plane.",
        H("Dissipative free-fermion roots in the upper half-plane"),
        Blocks(
            Definition("ffd-claw-free", "ClawFree", "Claw-free graphs", ClawDefinition(),
                "On printed p. 2: \"A graph is claw-free if it has no claw as an induced subgraph (Fig. 1(a)), and even-hole-free if it has no even hole as an induced subgraph (Fig. 1(b)).\" The formula excludes a center v with three distinct pairwise nonadjacent leaves a, b, c. In a simple graph adjacency already forces each leaf to differ from v."),
            Definition("ffd-even-hole-free", "EvenHoleFree", "Even-hole-free graphs", EvenHoleDefinition(),
                "On printed p. 2: \"A graph is claw-free if it has no claw as an induced subgraph (Fig. 1(a)), and even-hole-free if it has no even hole as an induced subgraph (Fig. 1(b)).\" An even hole is an induced cycle of even length at least four. The injection f lists its vertices with zero-based Fin m indices. The adjacency equivalence requires exactly the cyclic edges and forbids chords. The operator mod is natural-number remainder, and val extracts a Fin index's natural-number value."),
            Definition("ffd-simplicial", "Simplicial", "Simplicial cliques", SimplicialDefinition(),
                "On printed p. 3: \"The edge operator χ is associated with a clique K_s ⊆ V(G), i.e., a subset of mutually adjacent vertices.\" \"Equivalently, denoting the closed neighborhood of j by Γ[j] ≡ {j} ∪ {ℓ ∈ V(G) | A_jℓ = 1}, K_s is simplicial if and only if Γ[j] \\ K_s is a clique for all j ∈ K_s.\" K is K_s; neighborFinset gives the open neighborhood and insert j gives the closed neighborhood. Finsets are coerced to vertex sets for IsClique."),
            Definition("ffd-independence-polynomial", "P", "The weighted independence polynomial", PDefinition(),
                "Printed p. 3, Eq. (7): \"The independence polynomial is defined as\" P_G(x) ≡ Σ_{S∈S_G} (−x)^{|S|} Π_{j∈S} b_j², \"where S_G denotes the collection of all independent sets.\" The partition G U w is the sum over independent subsets of U of the product of w j. Thus the defining activity −C(b j²)X yields exactly Eq. (7) on the induced vertex domain U. C and X belong to ℝ[X], and b has real values."),
            Definition("ffd-dissipative-polynomial", "Pt", "The dissipative polynomial", PtDefinition(),
                "Printed p. 4, Eq. (16): P̃_G^±(u) ≡ P_G(u²) ± iγu P_{G\\K_s}(u²). Pt is the plus polynomial. The map ofRealHom embeds real coefficients into ℂ; comp substitutes X². The displayed coercion sends gamma : ℝ to ℂ. univ is the full finite vertex domain and univ \\ K deletes the clique."),
            Definition("ffd-root-location-claim", "claim", "The Fukai–Yoshida–Katsura expectation",
                Eq(Call("claim"), Parenthesized(ClaimBody())),
                "Printed p. 4, after Eq. (17): \"We expect Im ũ_k > 0 to hold for general ECF graphs, as observed numerically in the boundary-driven Fendley model, so that ε̃_k ≡ 1/ũ_k satisfies Im ε̃_k < 0.\" Here ũ_k are the roots of the plus polynomial in Eq. (16). ECF means even-hole-free and claw-free. Printed p. 3, Eq. (7): P_G(x) ≡ Σ_{S∈S_G} (−x)^{|S|} Π_{j∈S} b_j², \"where S_G denotes the collection of all independent sets.\" Printed p. 4, Eq. (16): P̃_G^±(u) ≡ P_G(u²) ± iγu P_{G\\K_s}(u²). Printed p. 3: \"Equivalently, denoting the closed neighborhood of j by Γ[j] ≡ {j} ∪ {ℓ ∈ V(G) | A_jℓ = 1}, K_s is simplicial if and only if Γ[j] \\ K_s is a clique for all j ∈ K_s.\" Printed p. 7, after Eq. (26): \"Equation (26) shows that N_k = 0 if P_G and P_{G\\K_s} share the root u_k². Throughout this work, we exclude this nongeneric case [80].\" The encoding quantifies every finite graph on Fin n, every real coupling vector b, every positive gamma, and every complex root u. The common-root exclusion quantifies all complex x. Polynomial aeval evaluates real polynomials at complex points; eval evaluates Pt in ℂ. No ordering or simplicity of the roots is assumed."),
            Describe.Lean(
                DescribeId.Create("ffd-root-location-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Every dissipative root has positive imaginary part"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Clique deletion splits the independent configurations according to their unique vertex in K, when present. Claw exclusion makes the neighbors of each deleted clique vertex into a simplicial clique in the remaining domain. For Im z < 0, induction on that domain constructs a multiplier r with Im r > 0 and P_U(z²) = z P_(U\\K)(z²) r. Its recursive expression is r = 1/z − Σ_(j∈K) b_j²/r_j, with every Im r_j > 0. Only nonzero recursive multipliers are divided by. A lower-half-plane root would force both independence polynomials to vanish; real roots are excluded by their real and imaginary parts, using P_U(0) = 1. The proof retains EvenHoleFree in the displayed statement but does not use it: the same root argument applies to every claw-free graph with a simplicial clique and the remaining hypotheses."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe Definition(string id, string name, string title,
        Formula expression, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(expression)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Diff(Formula a, Formula b) => Seq(a, Sp, Setminus, Sp, b);
    private static Formula Pow(Formula a) => new Formula.Power(a, D(2));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp, body);

    private static Formula GraphBind(Formula body) =>
        All("V", Call("Type"), All("G", Call("SimpleGraph", F.Id("V")), body));
    private static Formula FiniteGraphBind(Formula body, bool finite) => GraphBind(
        finite ? Instance("Fintype", F.Id("V"), Instance("DecidableEq", F.Id("V"),
            Instance("DecidableRel", Call("Adj", F.Id("G")), body))) :
        Instance("DecidableEq", F.Id("V"), Instance("DecidableRel", Call("Adj", F.Id("G")), body)));
    private static Formula Adj(Formula a, Formula b) => Call("Adj", F.Id("G"), a, b);

    private static Formula ClawDefinition()
    {
        var g = F.Id("G"); var v = F.Id("v"); var a = F.Id("a");
        var b = F.Id("b"); var c = F.Id("c");
        Formula body = Call("False");
        foreach (var premise in new[] { Not(Adj(b, c)), Not(Adj(a, c)), Not(Adj(a, b)),
            Adj(v, c), Adj(v, b), Adj(v, a), Ne(b, c), Ne(a, c), Ne(a, b) })
            body = Imp(premise, body);
        foreach (var variable in new[] { "c", "b", "a", "v" }) body = All(variable, F.Id("V"), body);
        return GraphBind(Iff(Call("ClawFree", g), body));
    }

    private static Formula EvenHoleDefinition()
    {
        var m = F.Id("m"); var f = F.Id("f"); var i = F.Id("i"); var j = F.Id("j");
        var cyclic = new Formula.Logic(
            Parenthesized(Eq(Call("mod", new Formula.Binary(Call("val", i), FormulaBinaryOperator.Add, D(1)), m), Call("val", j))),
            FormulaLogicOperator.Or,
            Parenthesized(Eq(Call("mod", new Formula.Binary(Call("val", j), FormulaBinaryOperator.Add, D(1)), m), Call("val", i))));
        var edges = All("i", Call("Fin", m), All("j", Call("Fin", m),
            Iff(Adj(new Formula.Apply(f, [i]), new Formula.Apply(f, [j])), cyclic)));
        var body = All("m", Nat(), Imp(Seq(D(4), Sp, Leq, Sp, m), Imp(Call("Even", m),
            All("f", Arrow(Call("Fin", m), F.Id("V")), Imp(Call("Injective", f), Not(edges))))));
        return GraphBind(Iff(Call("EvenHoleFree", F.Id("G")), body));
    }

    private static Formula SimplicialDefinition()
    {
        var k = F.Id("K"); var j = F.Id("j");
        var condition = And(Call("IsClique", F.Id("G"), Call("coe", k)),
            All("j", F.Id("V"), Imp(Mem(j, k), Call("IsClique", F.Id("G"),
                Call("coe", Parenthesized(Diff(Call("insert", j, Call("neighborFinset", F.Id("G"), j)), k)))))));
        return FiniteGraphBind(All("K", Call("Finset", F.Id("V")),
            Iff(Call("Simplicial", F.Id("G"), k), condition)), true);
    }

    private static Formula PDefinition()
    {
        var g = F.Id("G"); var u = F.Id("U"); var b = F.Id("b"); var j = F.Id("j");
        var activity = Parenthesized(Seq(Parenthesized(Seq(j, Sp, Colon, Sp, F.Id("V"))), Sp, Mapsto, Sp,
            Mul(new Formula.Negate(Call("C", Pow(new Formula.Apply(b, [j])))), F.Id("X"))));
        return FiniteGraphBind(All("U", Call("Finset", F.Id("V")), All("b", Arrow(F.Id("V"), Real()),
            Eq(Call("P", g, u, b), Call("partition", g, u, activity)))), false);
    }

    private static Formula Pterm(Formula domain) => Call("P", F.Id("G"), domain, F.Id("b"));
    private static Formula Deleted() => Parenthesized(Diff(Call("univ"), F.Id("K")));
    private static Formula PtDefinition()
    {
        var embeddedFull = Call("map", Call("ofRealHom"), Pterm(Call("univ")));
        var embeddedDeleted = Call("map", Call("ofRealHom"), Pterm(Deleted()));
        var gamma = Call("coe", F.Id("gamma"), Complex());
        var rhs = new Formula.Binary(Call("comp", embeddedFull, Pow(F.Id("X"))), FormulaBinaryOperator.Add,
            Mul(Mul(Call("C", Mul(Call("I"), gamma)), F.Id("X")),
                Call("comp", embeddedDeleted, Pow(F.Id("X")))));
        return FiniteGraphBind(All("K", Call("Finset", F.Id("V")), All("b", Arrow(F.Id("V"), Real()),
            All("gamma", Real(), Eq(Call("Pt", F.Id("G"), F.Id("K"), F.Id("b"), F.Id("gamma")), rhs)))), true);
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var g = F.Id("G"); var k = F.Id("K");
        var b = F.Id("b"); var gamma = F.Id("gamma"); var x = F.Id("x"); var u = F.Id("u");
        var common = All("x", Complex(), Not(And(Eq(Call("aeval", x, Pterm(Call("univ"))), D(0)),
            Eq(Call("aeval", x, Pterm(Deleted())), D(0)))));
        var root = Eq(Call("eval", u, Call("Pt", g, k, b, gamma)), D(0));
        Formula body = All("u", Complex(), Imp(root, Lt(D(0), Call("im", u))));
        body = Imp(common, body);
        body = Imp(Lt(D(0), gamma), body);
        body = Imp(Call("Simplicial", g, k), body);
        body = Imp(Call("EvenHoleFree", g), body);
        body = Imp(Call("ClawFree", g), body);
        return All("n", Nat(), All("G", Call("SimpleGraph", Call("Fin", n)),
            Instance("DecidableRel", Call("Adj", g), All("K", Call("Finset", Call("Fin", n)),
                All("b", Arrow(Call("Fin", n), Real()), All("gamma", Real(), body))))));
    }
}
