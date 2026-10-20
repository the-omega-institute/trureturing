using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class SamadzadehMojdehNadimiRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/samadzadeh2024pairedcoalition");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The perfect binary tree of height five has a paired coalition partition with five parts. Odd part sizes exclude paired domination of individual parts, while four explicit perfect matchings certify their unions. Thus its paired coalition number is at least five, contradicting the value three in Conjecture 1.",
        H("Five paired coalition parts in the height-five binary tree"),
        Blocks(
            Node("perfectBinaryTree", "The perfect binary tree", TreeFormula(),
                "Section 4.2, p. 9: \"A perfect binary tree is a binary tree in which all leaves have same distance to the root vertex.\" \"Given a perfect binary tree T, we call the distance between root vertex and each leaf, height of T.\" \"If T has height h, then we denote it by T(h).\" The root has depth zero. The vertex i : Fin (2^(h+1) - 1) has heap label i.val+1. The two children of label r have labels 2r and 2r+1. SimpleGraph.fromRel symmetrizes this relation and excludes loops; the resulting tree has all leaves at depth h. Subtraction in the vertex count is natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsPairedDominating", "Paired dominating sets", PairedDominatingFormula(),
                "Section 1, p. 2: \"A paired dominating set of a graph G = (V, E) is a dominating set S ⊆ V such that the induced subgraph G[S] contains a perfect matching.\" SimpleGraph.IsDominating says that every vertex belongs to S or has a neighbour in S. A subgraph M of G with M.verts = S and M.IsMatching has exactly one neighbour at every vertex in S, so it is a perfect matching in G[S]. The graph and set parameters range over an arbitrary vertex type.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsPairedCoalition", "Paired coalitions", CoalitionFormula(),
                "Definition 1.1, p. 2: \"A paired coalition in a graph G consists of two disjoint sets of vertices V₁ and V₂, neither of which is a paired dominating set but whose union V₁ ∪ V₂ is a paired dominating set.\" The sets A and B represent V₁ and V₂. All four requirements appear in the predicate.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsPCPartition", "Paired coalition partitions", PartitionFormula(),
                "Definition 1.2, p. 2: \"A paired coalition partition, abbreviated pc-partition, in a graph G is a vertex partition π = {V₁, V₂, . . . , Vₖ} such that every set Vᵢ of π is not a paired dominating set but forms a paired coalition with another set Vⱼ in π.\" The finset π consists of nonempty, pairwise disjoint sets covering all vertices. Each member has a distinct partner in the same finset. Coercing π to a set preserves its members; id is the identity map on its sets.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pcNumber", "The paired coalition number", NumberFormula(),
                "Definition 1.2, p. 2: \"The paired coalition number PC(G) equals the maximum order k of a pc-partition of G, and a pc-partition of G having order PC(G) is called a PC(G)-partition.\" The following paragraph says: \"As we will see later, not every graph G admits a pc-partition. In such situations we will say that PC(G) = 0.\" The natural-number supremum is over attained finset cardinalities, with sSup of the empty set equal to zero. For a finite graph these cardinalities are bounded, so this is the stated maximum. No decidability or finiteness assumption is needed to form the expression.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", Disp(EquivFormula(X("claim"), ClaimBody())),
                "Conjecture 1, Section 4.2, p. 12: \"If T(h) is a perfect binary tree with height h, then PC(T(h)) = 5 if h = 2; 3 if h is odd; 0 otherwise.\" The three alternatives are printed as a cases display. The statement ranges over every positive natural height h, with the height-two case tested first. In particular the odd-height clause gives PC(T(5)) = 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture is false", Disp(NotFormula(ClaimBody())),
                "Use heap labels 1 through 63, and R = {1,8,9,10,11,12,13,14,15}. Put A = ⋃ over r in R of {r,2r,2r+1}, and Bⱼ = {4r+j : r in R} for j = 0,1,2,3. These five disjoint sets cover all vertices and have sizes 27,9,9,9,9. A perfect matching has even vertex cardinality, so no individual part is paired dominating. A dominates the tree. For j = 0,1, match r to 2r+1 and 2r to 4r+j in each seven-vertex block; for j = 2,3, match r to 2r and 2r+1 to 4r+j. These matchings cover each A ∪ Bⱼ exactly. Hence each Bⱼ has partner A, and A has partner B₀. The resulting partition has order five. Its order belongs to the bounded set defining pcNumber, so 5 ≤ pcNumber (perfectBinaryTree 5), contradicting the conjectured value three. Only this height-five lower bound and the displayed negation are established here; the exact value and a uniform family remain separate questions. The same lower bound contradicts Lemma 4.10, p. 9, which states PC(T(h)) ≤ 4 for h ≥ 3. The authors' final remark on p. 12 seeks to exclude order four, which does not exclude order five. No conclusion is drawn here about the independent path, cycle or other tree results.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("samadzadeh-mojdeh-nadimi-2024-paired-coalition-binary-tree"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("smn-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Field(Formula value, string name) => Seq(value, Dot, Operatorname, Grp(X(name)));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula SetOf(Formula type) => Call("Set", type);
    private static Formula FinsetOf(Formula type) => Call("Finset", type);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Graph(Formula type) => Call("SimpleGraph", type);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula EquivFormula(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula NotFormula(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula LambdaIn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Operatorname, Grp(X("fun")), Sp,
            Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Union(Formula a, Formula b) => Seq(a, Sp, Cup, Sp, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Sp, Colon, Sp, type));
    private static Formula Paired(Formula graph, Formula set) => Call("IsPairedDominating", graph, set);
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Operatorname, Grp(X("if")), Sp, condition, Sp,
            Operatorname, Grp(X("then")), Sp, yes, Sp, Operatorname, Grp(X("else")), Sp, no));
    private static Formula OverGraph(Formula body) =>
        All("V", X("Type"), All("G", Graph(X("V")), body));

    private static Formula TreeFormula()
    {
        Formula h = X("h"), x = X("x"), y = X("y");
        Formula size = new Formula.Binary(new Formula.Power(D(2), Add(h, D(1))), FormulaBinaryOperator.Subtract, D(1));
        Formula xv = Add(Call("val", x), D(1)), yv = Add(Call("val", y), D(1));
        Formula relation = Or(Equal(yv, Mul(D(2), Parenthesized(xv))),
            Equal(yv, Add(Mul(D(2), Parenthesized(xv)), D(1))));
        return Disp(All("h", Nat, Equal(Call("perfectBinaryTree", h),
            App(Qualified("SimpleGraph", "fromRel"), LambdaIn("x", Fin(size), LambdaIn("y", Fin(size), relation))))));
    }

    private static Formula PairedDominatingFormula()
    {
        Formula g = X("G"), s = X("S"), m = X("M");
        Formula body = And(App(Qualified("SimpleGraph", "IsDominating"), g, s),
            Some("M", Field(g, "Subgraph"), And(Equal(Field(m, "verts"), s), Field(m, "IsMatching"))));
        return Disp(OverGraph(All("S", SetOf(X("V")), EquivFormula(Paired(g, s), body))));
    }

    private static Formula CoalitionFormula()
    {
        Formula g = X("G"), a = X("A"), b = X("B"), sv = SetOf(X("V"));
        Formula body = And(Call("Disjoint", a, b), And(NotFormula(Paired(g, a)),
            And(NotFormula(Paired(g, b)), Paired(g, Parenthesized(Union(a, b))))));
        return Disp(OverGraph(All("A", sv, All("B", sv,
            EquivFormula(Call("IsPairedCoalition", g, a, b), body)))));
    }

    private static Formula PartitionFormula()
    {
        Formula g = X("G"), pi = X("pi"), a = X("A"), b = X("B"), v = X("v");
        Formula sv = SetOf(X("V"));
        Formula nonempty = All("A", sv, Imp(Member(a, pi), Field(a, "Nonempty")));
        Formula disjoint = App(Field(Cast(pi, SetOf(sv)), "PairwiseDisjoint"), X("id"));
        Formula cover = All("v", X("V"), Some("A", sv, And(Member(a, pi), Member(v, a))));
        Formula partners = All("A", sv, Imp(Member(a, pi), And(NotFormula(Paired(g, a)),
            Some("B", sv, And(Member(b, pi), And(NotFormula(Equal(b, a)), Call("IsPairedCoalition", g, a, b)))))));
        return Disp(OverGraph(All("pi", FinsetOf(sv), EquivFormula(Call("IsPCPartition", g, pi),
            And(nonempty, And(disjoint, And(cover, partners)))))));
    }

    private static Formula NumberFormula()
    {
        Formula k = X("k"), pi = X("pi"), g = X("G");
        Formula orders = Seq(OpenBrace, k, Sp, Colon, Sp, Nat, Sp, Mid, Sp,
            Some("pi", FinsetOf(SetOf(X("V"))),
                And(Call("IsPCPartition", g, pi), Equal(Field(pi, "card"), k))), CloseBrace);
        return Disp(OverGraph(Equal(Call("pcNumber", g), Call("sSup", orders))));
    }

    private static Formula ClaimBody()
    {
        Formula h = X("h");
        return All("h", Nat, Imp(Leq(D(1), h), Equal(Call("pcNumber", Call("perfectBinaryTree", h)),
            IfThenElse(Equal(h, D(2)), D(5), IfThenElse(Call("Odd", h), D(3), D(0))))));
    }
}
