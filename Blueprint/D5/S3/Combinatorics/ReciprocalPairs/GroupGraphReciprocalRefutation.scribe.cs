using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ReciprocalPairs;

internal sealed class GroupGraphReciprocalRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.";
    private static readonly LibraryNoteRef Campbell = LibraryNoteRef.Create("D5/L/GraphInvariants/campbell2020reciprocal");
    private static readonly LibraryNoteRef CameronSemeraro = LibraryNoteRef.Create("D5/L/GraphInvariants/cameronsemeraro2018cycle");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sign-coupled group on three edges and two four-cliques refutes the reciprocal-pair classification.",
        H("Campbell's group-graph reciprocal-pair conjecture"),
        Blocks(
            Def("IsAut", "Automorphisms", AutomorphismFormula(),
                "Page 4: \"By definition, g is an element of the automorphism group if and only if {i, j} and {g(i), g(j)} are both edges in Γ.\" The permutation preserves adjacency in both directions.", AssessedProvenance.FromLiterature(Campbell)),
            Def("cyclePoly", "Cycle polynomial", CyclePolynomialFormula(),
                "Page 1: \"The cycle polynomial of a finite permutation group G acting on a set Ω of size n is\" F_G(x) = Σ_{g∈G} x^{c(g)}, \"where c(g) is the number of cycles (including fixed points) of g on Ω.\" SameCycle identifies vertices in a common permutation cycle, including each fixed vertex as a singleton. The coefficients are integers.", AssessedProvenance.FromLiterature(Campbell)),
            Def("fixedColourings", "Fixed proper colourings", FixedColouringsFormula(),
                "Page 1: \"A proper colouring of a graph is a map from the vertex set to the set of colourings such that no two adjacent vertices have the same colour.\" Page 1: \"The chromatic polynomial PΓ/g(x) is the polynomial which counts proper colourings of Γ fixed by g.\" Colours are Fin c; each map is counted once, with adjacent vertices differently coloured and f(g(v)) = f(v).", AssessedProvenance.FromLiterature(Campbell)),
            Def("IsReciprocal", "Reciprocal pairs", ReciprocalFormula(),
                "Page 2: \"We call a group-graph pair (Γ, G) a reciprocal pair if the relation\" PΓ,G(x) = (−1)^n F_G(−x) \"holds for a simple graph Γ with n vertices and where G is an automorphism group of Γ.\" The equation is evaluated at every positive natural number c. Equality at all these integers is equality of the corresponding polynomials.", AssessedProvenance.FromLiterature(Campbell)),
            Def("Reducible", "A sufficient obstruction to irreducibility", ReducibleFormula(),
                "Page 3: \"A reciprocal pair (Γ, G) is irreducible is there is no non-trivial decomposition Γ = Γ1 ∪ Γ2 ∪ ... ∪ Γn and subgroups Gi ≤ G with Gi ≤ Aut(Γi) such that either\" \"1. G = G1 × ... × Gn with each (Γi, Gi) a reciprocal pair,\" \"2. Gi ≅ Gj and Γi ≅ Γj for all i ≠ j and G = G0 ≀ H for some H ≤ Sn and G0 ≅ Gi for all i.\" The displayed predicate allows more decompositions: the first branch requires only generation by subgroups fixing other parts; the second requires only isomorphism of the induced part graphs. Surjectivity and m ≥ 2 make the parts nonempty and the decomposition nontrivial.", AssessedProvenance.FromLiterature(Campbell)),
            Def("IsIrreducible", "Irreducibility", IrreducibleFormula(),
                "No decomposition satisfies either of the two conditions in Reducible. Since those conditions include every decomposition in the definition on page 3, this predicate implies the source's irreducibility.", AssessedProvenance.FromLiterature(Campbell)),
            Def("Listed", "The listed graph classes", ListedFormula(),
                "Page 3: \"1. (Γ, G) is one of the two trivial cases: (a) Γ is a null graph and G is any group with no odd permutations, (b) Γ is the complete graph with n vertices and G = Sn. 2. Γ is a 4-cycle and G ≅ Aut(Γ). 3. Γ is a k-star and G is defined in Theorem 1.\" The predicate drops the group restrictions and retains these four graph conditions. A k-star has a nonempty proper centre K; distinct vertices are adjacent exactly when at least one lies in K.", AssessedProvenance.FromLiterature(Campbell)),
            Def("claim", "The conjecture", ClaimFormula(),
                "Conjecture, page 3 (verbatim): \"Conjecture: Let (Γ, G) be an irreducible reciprocal pair. Then one of the following hold: 1. (Γ, G) is one of the two trivial cases: (a) Γ is a null graph and G is any group with no odd permutations, (b) Γ is the complete graph with n vertices and G = Sn. 2. Γ is a 4-cycle and G ≅ Aut(Γ). 3. Γ is a k-star and G is defined in Theorem 1.\" V is a finite vertex type, Gamma denotes Γ, and G is a finite subgroup of Equiv.Perm V. Automorphisms, positive-integer evaluations, irreducibility and the listed classes have exactly the meanings displayed above. The broader decomposition test and broader listed conclusion make claim a consequence of the source conjecture.", AssessedProvenance.FromLiterature(Campbell)),
            Node("result", "Refutation", Seq(Neg, Sp, Name("claim")),
                "The graph 3K₂ ⊔ 2K₄ has fourteen vertices. The group permits all internal clique permutations, with S₃ acting on the three edges naturally and on the two four-cliques through its sign. It is reciprocal: nonproper colourings cancel under an edge transposition, while every permutation fixing a proper colouring has sign +1. Its two clique layers cannot generate the whole coupled group from subgroups supported on separate parts. Pairwise isomorphic parts would have equal even cardinalities, which is incompatible with fourteen vertices and between two and five parts. An edge and a nonedge exclude the two trivial graph classes, cardinality excludes the four-cycle, and the absence of a universal vertex excludes every k-star. The general cycle-polynomial and reciprocity background is Cameron–Semeraro (2018).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Campbell, CameronSemeraro),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("campbell-2020-group-graph-reciprocal-pairs"), ResolutionKind.Refuted))), []));

    private static DocumentBlock Def(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Node(name, title, formula, prose, DescribeRole.Definition, provenance);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("campbell-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(Seq(Lex(owner), Dot, Lex(name))));
    private static Formula Lex(string name) => name switch
    {
        "Equiv.Perm.SameCycle" => Seq(F.Id("Equiv"), Dot, F.Id("Perm"), Dot, F.Id("SameCycle")),
        _ => F.Id(name),
    };
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(F.LambdaLower, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => new Formula.Integers();
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Perm(Formula type) => App(Qualified("Equiv", "Perm"), type);
    private static Formula Subgroup(Formula type) => Call("Subgroup", Perm(type));
    private static Formula Graph(Formula type) => Call("SimpleGraph", type);
    private static Formula V => F.Id("V");
    private static Formula Gamma => F.Id("Gamma");
    private static Formula G => F.Id("G");
    private static Formula g => F.Id("g");
    private static Formula u => F.Id("u");
    private static Formula v => F.Id("v");
    private static Formula c => F.Id("c");
    private static Formula f => F.Id("f");
    private static Formula Card(Formula type) => App(Qualified("Fintype", "card"), type);
    private static Formula SetCard(Formula set) => App(Qualified("Finset", "card"), set);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Adj(Formula graph, Formula a, Formula b) => App(Qualified("SimpleGraph", "Adj"), graph, a, b);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(Sum, Underscore, Grp(Seq(F.Id(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, F.Id(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula VertexBind(Formula body) => All("V", F.Id("Type"), Inst(Call("Fintype", V), Inst(Call("DecidableEq", V), body)));
    private static Formula BareGraphBind(Formula body) => All("V", F.Id("Type"), All("Gamma", Graph(V), body));
    private static Formula BareGroupBind(Formula body) => BareGraphBind(All("G", Subgroup(V), body));
    private static Formula FiniteBind(Formula body) => All("V", F.Id("Type"), Inst(Call("Fintype", V), body));
    private static Formula GraphBind(Formula body) => VertexBind(All("Gamma", Graph(V), body));
    private static Formula GroupBind(Formula body) => GraphBind(All("G", Subgroup(V), body));
    private static Formula Proper(Formula colouring) => All("u", V, All("v", V, Imp(Adj(Gamma, u, v), Ne(App(colouring, u), App(colouring, v)))));
    private static Formula Fixed(Formula colouring, Formula permutation) => All("v", V, Eq(App(colouring, App(permutation, v)), App(colouring, v)));
    private static Formula AutomorphismFormula() => BareGraphBind(All("g", Perm(V), Iff(Call("IsAut", Gamma, g), All("u", V, All("v", V, Iff(Adj(Gamma, App(g, u), App(g, v)), Adj(Gamma, u, v)))))));
    private static Formula CyclePolynomialFormula()
    {
        Formula cycles = Card(Call("Quotient", App(Qualified("Equiv.Perm.SameCycle", "setoid"), Cast(Val(g), Perm(V)))));
        Formula sum = SumOver("g", G, new Formula.Power(Cast(Qualified("Polynomial", "X"), Call("Polynomial", Int())), cycles));
        return FiniteBind(All("G", Subgroup(V), Inst(Call("Fintype", G), Eq(Call("cyclePoly", G), sum))));
    }
    private static Formula FixedColouringsFormula()
    {
        Formula maps = Fn(V, Fin(c));
        Formula predicate = Lambda("f", maps, And(Proper(f), Fixed(f, g)));
        Formula set = App(Qualified("Finset", "filter"), predicate, Cast(Qualified("Finset", "univ"), Call("Finset", maps)));
        return GraphBind(All("g", Perm(V), All("c", Nat(), Eq(Call("fixedColourings", Gamma, g, c), set))));
    }
    private static Formula ReciprocalFormula()
    {
        Formula sum = SumOver("g", G, SetCard(Call("fixedColourings", Gamma, Cast(Val(g), Perm(V)), c)));
        Formula rhs = new Formula.Binary(new Formula.Power(Cast(Seq(Minus, D(1)), Int()), Card(V)), FormulaBinaryOperator.Multiply,
            App(Qualified("Polynomial", "eval"), Seq(Minus, Cast(c, Int())), Call("cyclePoly", G)));
        return GroupBind(Inst(Call("Fintype", G), Iff(Call("IsReciprocal", Gamma, G), All("c", Nat(), Imp(Lt(D(0), c), Eq(Cast(sum, Int()), rhs))))));
    }
    private static Formula ReducibleFormula()
    {
        Formula m = F.Id("m"), part = F.Id("part"), i = F.Id("i"), j = F.Id("j"), gi = F.Id("Gi");
        Formula noCross = All("u", V, All("v", V, Imp(Adj(Gamma, u, v), Eq(App(part, u), App(part, v)))));
        Formula sub = All("i", Fin(m), Le(App(gi, i), G));
        Formula supported = All("i", Fin(m), All("g", Perm(V), Imp(Mem(g, App(gi, i)), All("v", V, Imp(Ne(App(part, v), i), Eq(App(g, v), v))))));
        Formula union = App(Qualified("Set", "iUnion"), Lambda("i", Fin(m), Cast(App(gi, i), Call("Set", Perm(V)))));
        Formula generated = Eq(App(Qualified("Subgroup", "closure"), union), G);
        Formula factors = Ex("Gi", Fn(Fin(m), Subgroup(V)), And(sub, And(supported, generated)));
        Formula PartGraph(Formula label) => App(Qualified("SimpleGraph", "induce"), SetOf("v", V, Eq(App(part, v), label)), Gamma);
        Formula iso = Call("Nonempty", App(Qualified("SimpleGraph", "Iso"), PartGraph(i), PartGraph(j)));
        Formula equalParts = All("i", Fin(m), All("j", Fin(m), iso));
        Formula parts = Ex("part", Fn(V, Fin(m)), And(App(Qualified("Function", "Surjective"), part), And(noCross, Or(factors, equalParts))));
        return BareGroupBind(Iff(Call("Reducible", Gamma, G), Ex("m", Nat(), And(Le(D(2), m), parts))));
    }
    private static Formula IrreducibleFormula() => BareGroupBind(Iff(Call("IsIrreducible", Gamma, G), Not(Call("Reducible", Gamma, G))));
    private static Formula ListedFormula()
    {
        Formula k = F.Id("k"), K = F.Id("K");
        Formula empty = All("u", V, All("v", V, Not(Adj(Gamma, u, v))));
        Formula complete = All("u", V, All("v", V, Imp(Ne(u, v), Adj(Gamma, u, v))));
        Formula cycle = Call("Nonempty", App(Qualified("SimpleGraph", "Iso"), Gamma, App(Qualified("SimpleGraph", "cycleGraph"), D(4))));
        Formula centre = Ex("K", Call("Finset", V), And(Eq(SetCard(K), k), All("u", V, All("v", V, Iff(Adj(Gamma, u, v), And(Ne(u, v), Or(Mem(u, K), Mem(v, K))))))));
        Formula star = Ex("k", Nat(), And(Le(D(1), k), And(Lt(k, Card(V)), centre)));
        return FiniteBind(All("Gamma", Graph(V), All("G", Subgroup(V), Iff(Call("Listed", Gamma, G), Or(empty, Or(complete, Or(cycle, star)))))));
    }
    private static Formula ClaimFormula()
    {
        Formula aut = All("g", Perm(V), Imp(Mem(g, G), Call("IsAut", Gamma, g)));
        Formula body = Imp(aut, Imp(Call("IsReciprocal", Gamma, G), Imp(Call("IsIrreducible", Gamma, G), Call("Listed", Gamma, G))));
        Formula quantified = VertexBind(All("Gamma", Graph(V), Inst(Call("DecidableRel", App(Qualified("SimpleGraph", "Adj"), Gamma)), All("G", Subgroup(V), Inst(Call("Fintype", G), body)))));
        return Iff(Name("claim"), quantified);
    }
}
