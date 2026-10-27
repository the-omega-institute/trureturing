using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class DegenerateGraphBalanceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.";
    private static readonly LibraryNoteRef Survey = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");
    private static readonly LibraryNoteRef Balance = LibraryNoteRef.Create("D5/L/QuadraticForms/alshatnawicostoyaviruel2026grothendieck");

    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula x, Formula type, Formula body) => Seq(Exists, Sp,
        Parenthesized(Seq(x, Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Lam(Formula x, Formula type, Formula body) => Seq(X("fun"), Sp,
        Parenthesized(Seq(x, Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Sp, Colon, Sp, type));
    private static Formula Z => new Formula.Integers();
    private static Formula NN => Seq(Mathbb, Grp(X("N")));
    private static Formula Type => Name("Type");
    private static Formula K => X("k");
    private static Formula V => X("V");
    private static Formula N => X("n");
    private static Formula P => X("p");
    private static Formula I => X("i");
    private static Formula J => X("j");
    private static Formula FinN => Call("Fin", N);
    private static Formula PathType => Call("Path", Gamma, N);
    private static Formula Vertex(Formula i) => App(Qualified("Path", "vertex"), P, i);
    private static Formula Edge(Formula i) => App(Qualified("Path", "edge"), P, i);
    private static Formula Start => Vertex(App(Qualified("Fin", "castSucc"), I));
    private static Formula End => Vertex(App(Qualified("Fin", "succ"), I));
    private static Formula Forward => Eq(Edge(I), Pair(Start, End));
    private static Formula Backward => Eq(Edge(I), Pair(End, Start));
    private static Formula CycleBody => Eq(Vertex(D(0)), Vertex(App(Qualified("Fin", "last"), N)));
    private static Formula Count(Formula predicate) => Cast(App(Qualified("Finset", "card"),
        App(Qualified("Finset", "filter"), Lam(I, FinN, predicate),
            Cast(Qualified("Finset", "univ"), Call("Finset", FinN)))), Z);
    private static Formula CycleSet => Seq(OpenBrace, X("z"), Sp, Colon, Sp, Z, Sp, Mid, Sp,
        Some(N, NN, Some(P, PathType, And(Call("IsCycle", P),
            Eq(X("z"), Cast(App(Qualified("Int", "natAbs"), Call("pathBalance", P)), Z))))), CloseBrace);
    private static Formula AlgebraContext(Formula body) => All(K, Type,
        Instance(Call("Field", K), All(V, Type, Instance(Call("AddCommGroup", V),
            Instance(Call("Module", K, V), body)))));
    private static Formula LMap(Formula a, Formula b) =>
        Call("LinearMap", App(Qualified("RingHom", "id"), K), a, b);
    private static Formula Product => LMap(V, LMap(V, V));
    private static Formula Basis(Formula index) => App(Qualified("Module", "Basis"), index, K, V);
    private static Formula Natural(Formula b, Formula index) => All(I, index, All(J, index,
        Imp(Ne(I, J), Eq(App(Mu, App(b, I), App(b, J)), D(0)))));
    private static Formula WholeClaim => AlgebraContext(Instance(Call("FiniteDimensional", K, V),
        All(Mu, Product, Imp(App(Qualified("DerivationAnnihilatorObstruction", "IsEvolutionAlgebra"), Mu),
            All(Iota, Type, All(Kappa, Type, Instance(Call("Fintype", Iota), Instance(Call("Fintype", Kappa),
                All(X("B"), Basis(Iota), All(X("F"), Basis(Kappa), Imp(Natural(X("B"), Iota),
                    Imp(Natural(X("F"), Kappa), Eq(Call("graphBalance", Call("associatedGraph", Mu, X("B"))),
                        Call("graphBalance", Call("associatedGraph", Mu, X("F"))))))))))))))));
    private static Formula GraphContext(Formula body) => All(V, Type, All(Gamma, Call("Digraph", V), body));
    private static Formula PathContext(Formula body) => GraphContext(All(N, NN, All(P, PathType, body)));
    private static Formula Generator(Formula ideal) => App(Seq(Name("Submodule"), Dot,
        Name("IsPrincipal"), Dot, Name("generator")), ideal);
    private static DocumentBlock.Describe Desc(string name, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    public DocumentDefinition Create()
    {
        var coefficient = App(Seq(Name("Module"), Dot, Name("Basis"), Dot, Name("repr")),
            X("B"), App(Mu, App(X("B"), I), App(X("B"), I)), J);
        var graphFormula = AlgebraContext(All(Iota, Type, All(Mu, Product, All(X("B"), Basis(Iota),
            Eq(Call("associatedGraph", Mu, X("B")),
                Seq(OpenBrace, Name("Adj"), Sp, Colon, F.Eq, Sp,
                    Lam(I, Iota, Lam(J, Iota, Ne(coefficient, D(0)))), CloseBrace))))));
        var vertex = X("vertex");
        var edge = X("edge");
        var start = App(vertex, App(Qualified("Fin", "castSucc"), I));
        var end = App(vertex, App(Qualified("Fin", "succ"), I));
        var pathFormula = GraphContext(All(N, NN, Seq(Call("Path", Gamma, N), Sp, Colon, F.Eq, Sp,
            OpenBrace, vertex, Sp, Colon, Sp, Arrow(Call("Fin", Add(N, D(1))), V), Semi, Sp,
            edge, Sp, Colon, Sp, Arrow(FinN, Seq(V, Sp, Times, Sp, V)), Semi, Sp,
            Name("isEdge"), Sp, Colon, Sp, All(I, FinN, App(Qualified("Digraph", "Adj"), Gamma,
                App(Qualified("Prod", "fst"), App(edge, I)), App(Qualified("Prod", "snd"), App(edge, I)))),
            Semi, Sp, Name("traverses"), Sp, Colon, Sp, All(I, FinN,
                Or(Eq(App(edge, I), Pair(start, end)), Eq(App(edge, I), Pair(end, start)))), CloseBrace)));
        var balanceFormula = GraphContext(Eq(Call("graphBalance", Gamma),
            App(Qualified("Int", "natAbs"), Generator(App(Qualified("Ideal", "span"), CycleSet)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Degenerate natural bases with graph balances two and one.",
            H("An annihilator shear changes graph balance"), Blocks(
                Paragraph(Text("Over any field take the natural basis (a,b,u,z), with a squared equal to b, b squared equal to a+u, u squared equal to z, z squared equal to zero, and all mixed products zero. Replacing a by a+z preserves naturality. In the second basis b squared equals (a+z)+u-z. The coefficient -1 remains nonzero in characteristic two.")),
                Desc("associatedGraph", graphFormula,
                    "Survey section 1.1, page 3: “To A and B one attaches the directed graph Γ(A,B) with vertex set Λ and an arrow i→j whenever ωᵢⱼ≠0 [48]; this graph is the single most useful tool of the theory.” The row coefficient is obtained by applying Module.Basis.repr to the square of B(i). The displayed record specifies the entire adjacency relation.",
                    AssessedProvenance.FromLiterature(Survey)),
                Desc("Path", pathFormula,
                    "Definition 2.2, page 4: “A path in Γ is a sequence γ=(v₀,e₁,v₁,…,vₙ₋₁,eₙ,vₙ), n ≥ 0, with v₀,…,vₙ∈V and e₁,…,eₙ∈E such that, for each i∈{1,…,n}, either eᵢ=(vᵢ₋₁,vᵢ) (the edge is traversed forwards) or eᵢ=(vᵢ,vᵢ₋₁) (traversed backwards).” Vertices use Fin(n+1) and edges use Fin n, starting at zero. Fin.castSucc and Fin.succ give the endpoints of edge i. The actual directed arrow is retained, including when opposing arrows both exist.",
                    AssessedProvenance.FromLiterature(Balance)),
                Desc("IsCycle", PathContext(Iff(Call("IsCycle", P), CycleBody)),
                    "Definition 2.2, page 4: “A (non-simple) cycle is a path with v₀=vₙ.” The last vertex is indexed by Fin.last n; paths of length zero are included.",
                    AssessedProvenance.FromLiterature(Balance)),
                Desc("pathBalance", PathContext(Eq(Call("pathBalance", P), Sub(Count(Forward), Count(Backward)))),
                    "Definition 2.2, page 4: “The balance of γ is the integer b(γ)=#{ i : eᵢ=(vᵢ₋₁,vᵢ) }−#{ i : eᵢ=(vᵢ,vᵢ₋₁) }”. Both finite cardinalities are cast to integers before subtraction. A loop belongs to both sets and contributes zero. Both graphs used here have no loops.",
                    AssessedProvenance.FromLiterature(Balance)),
                Desc("graphBalance", balanceFormula,
                    "Definition 2.4, page 4: “The balance of Γ is the greatest common divisor of the absolute values of the balances of its cycles, b(Γ)=gcd{ |b(γ)| : γ a cycle in Γ }.” The integer ideal is generated by the natural absolute values, cast to integers, of all finite closed-path balances. The natural absolute value of its generator is this gcd. There is no length cutoff; the gcd is zero when every balance is zero. The graph and path definitions also apply to infinite vertex types, although claim uses finite bases.",
                    AssessedProvenance.FromLiterature(Balance)),
                Desc("claim", Iff(X("claim"), WholeClaim),
                    "Question 27, page 24: “Is the balance independent of the natural basis for arbitrary (possibly degenerate) evolution algebras?” Section 1.1, page 3: “Unless stated otherwise, algebras are finite-dimensional.” The assertion quantifies every field k, every finite-dimensional k-module V with bilinear multiplication μ satisfying IsEvolutionAlgebra, and every pair B,F of natural bases indexed by finite types ι,κ. No nondegeneracy, perfectness, characteristic or connectedness restriction is added.",
                    AssessedProvenance.FromLiterature(Survey)),
                Desc("result", new Formula.Not(Parenthesized(WholeClaim)),
                    "In the first graph the arrows are 0→1, 1→0, 1→2 and 2→3. The heights (0,1,0,1) in ZMod 2 increase along every arrow; telescoping along every closed signed path forces even balance. The directed two-cycle has balance two, so the graph balance is two. The second graph adds 1→3. Its path 1→2→3←1 has balance one, so its graph balance is one. Both bases are natural over every field. Specializing to the rational field contradicts the universal equality. The mechanism is the shear through the annihilator, which changes square-support coordinates while preserving the mixed-product equations. This addresses the final assertion of Question 27.",
                    AssessedProvenance.FromRepo(Survey, Balance), DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(ProblemSlugRef.Create("kmv27-evobalance"),
                        ResolutionKind.Refuted)))));
    }
}
