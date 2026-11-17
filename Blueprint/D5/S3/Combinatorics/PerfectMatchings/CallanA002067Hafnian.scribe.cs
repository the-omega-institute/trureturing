using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class CallanA002067HafnianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/callan2017a002067");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both of Callan's 2017 A002067 assertions hold for all natural indices, including the empty matching and empty path.",
        H("Callan's A002067 hafnian and Dyck identities"),
        Blocks(
            Node("hafnian", "Hafnian of the constant-row array", "hafnian", HafnianFormula(),
                "OEIS A002067, Callan COMMENTS (unnumbered entry, no page number): \"a(n) is the Hafnian of the triangular array (u(i,j))_{1 <= i < j <= 2n} with u(i,j)=i. The Hafnian is the same as the Pfaffian except without the alternating signs just as the permanent of a matrix is the determinant without the signs.\" A matching is a subgraph of the complete graph on Fin(2*n). Vertex i has source label i.val+1. The nested product includes each edge once, at its smaller endpoint; the empty product is one.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The two source assertions", "claim", Equal(V("claim"), ClaimBody()),
                "OEIS A002067, Callan COMMENTS (unnumbered entry, no page number): \"a(n) is the Hafnian of the triangular array (u(i,j))_{1 <= i < j <= 2n} with u(i,j)=i. The Hafnian is the same as the Pfaffian except without the alternating signs just as the permanent of a matrix is the determinant without the signs.\" \"a(n) is the total weight of Dyck n-paths with weight defined as follows. Given a Dyck path, for each upstep, record its position in the path and the height of its upper endpoint; then multiply together all of these positions and heights. For example, the Dyck 4-path P = UUDUUDDD has upsteps in positions 1,2,4,5 ending at heights 1,2,2,3 respectively, and hence weight(P) = 480. (In fact the positions determine the heights because, for the k-th upstep, position + height = 2k.)\" The proposition includes existence of the sequence and quantifies over every solution of the NAME recurrence and every n : Nat. Empty matching and path weights are one.", AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both identities for every index", "result", ClaimBody(),
                "Adjoining the largest label to an involution either creates a fixed point or joins it to an existing fixed point. The resulting weighted generating polynomial obeys derivative plus (r+1)X multiplication. Evaluation at zero retains precisely the fixed-point-free involutions, which correspond to perfect matchings. The same polynomial counts weighted Dyck paths and its even constant terms satisfy the source convolution.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("callan-a002067"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("callan-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumIn(Formula binder, Formula body) => Seq(new Formula.Subscript(Sum, binder), Sp, body);
    private static Formula ProdIn(Formula binder, Formula body) => Seq(new Formula.Subscript(Prod, binder), Sp, body);
    private static Formula Dyck(string name, params Formula[] args) => Qualified("CallanA002067Dyck", name, args);
    private static Formula Labels(Formula n) => Call("Fin", Mul(D(2), n));
    private static Formula Graph(Formula n) => Call("SimpleGraph", Labels(n));
    private static Formula Subgraphs(Formula n) => Qualified("SimpleGraph", "Subgraph", Parenthesized(Seq(Seq(Operatorname, Grp(V("Top"), Dot, V("top"))), Colon, Sp, Graph(n))));
    private static Formula HafnianFormula()
    {
        var n = V("n"); var m = V("M"); var i = V("i"); var j = V("j");
        var selected = And(new Formula.Relation(i, FormulaRelationOperator.LessThan, j),
            App(Seq(Operatorname, Grp(V("SimpleGraph"), Dot, V("Subgraph"), Dot, V("Adj"))), m, i, j));
        var weight = ProdIn(Seq(i, Colon, Sp, Labels(n)), ProdIn(Seq(j, Colon, Sp, Labels(n)),
            Call("ite", selected, Add(Call("val", i), D(1)), D(1))));
        return All("n", N(), Equal(Call("hafnian", n), SumIn(Seq(m, Colon, Sp, Subgraphs(n)),
            Call("ite", App(Seq(Operatorname, Grp(V("SimpleGraph"), Dot, V("Subgraph"), Dot, V("IsPerfectMatching"))), m), weight, D(0)))));
    }
    private static Formula ClaimBody()
    {
        var a = V("a"); var n = V("n");
        return And(ExistsIn("a", Arrow(N(), N()), Dyck("IsSourceSequence", a)),
            All("a", Arrow(N(), N()), Imp(Dyck("IsSourceSequence", a), All("n", N(),
                And(Equal(App(a, n), Call("hafnian", n)), Equal(App(a, n), Dyck("weightedDyckSum", n)))))));
    }
}
