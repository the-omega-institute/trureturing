using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoMcPhersonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoMcPherson.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/kok2014mcpherson");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The McPherson number of the finite Jaco graph J_n(1) is b_n - 1, so it is nonrepetitive exactly when the outdegree b_n is.",
        H("The McPherson number of Jaco graphs"),
        Blocks(
            Node("mcpherson-explode", "A vertex explosion", "explode",
                Disp(Iff(Call("Adj", Call("explode", F.Id("H"), F.Id("w")), F.Id("a"), F.Id("b")),
                    Or(Call("Adj", F.Id("H"), F.Id("a"), F.Id("b")),
                        And(new Formula.Relation(F.Id("a"), FormulaRelationOperator.NotEqual, F.Id("b")),
                            Or(Equal(F.Id("a"), F.Id("w")), Equal(F.Id("b"), F.Id("w"))))))),
                "explode H w joins the exploding vertex w to every other vertex; arcs created by the explosion are recorded through the underlying graph only, since the McPherson number depends only on it.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mcpherson-run", "The McPherson recursion", "run",
                Disp(Equal(Call("run", F.Id("G"), F.Id("L")), Call("foldl", F.Id("explode"), F.Id("G"), F.Id("L")))),
                "run G L lets the vertices of the list L explode in order, starting from G.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mcpherson-number", "The McPherson number", "mcpherson",
                Disp(Equal(Call("Upsilon", F.Id("G")), Call("min", Seq(F.OpenBrace, Call("length", F.Id("L")), Colon, Sp,
                    Equal(Call("run", F.Id("G"), F.Id("L")), F.Id("K")), F.CloseBrace)))),
                "mcpherson G is the least length of an explosion list after which the underlying graph is complete (K is the complete graph on the vertices of G); this is the McPherson number of Kok and Susanth.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mcpherson-result", "The McPherson number of J_n(1)", "result", ResultFormula(),
                "After the explosions of L, two distinct vertices are adjacent exactly when they were adjacent in G or one of them exploded; hence the underlying graph is complete exactly when the non-exploding vertices form a clique of G, whatever the order of the explosions. For the finite Jaco graph J_n(1), with R_i=i+b_i and b_i=floor((i+1)/phi), JacoEndpointBeatty.beatty_threshold gives n<=R_i exactly when b_n<=i, so the labels at least b_n form a clique and the b_n-1 labels below b_n suffice. Conversely, a clique whose least label is m lies in [m,min(n,R_m)]: if m>=b_n it has at most n+1-b_n vertices, and if m<b_n it has at most b_m+1<=b_(b_n-1)+1<=n+1-b_n vertices, again by the threshold; so at least b_n-1 vertices must explode. Hence Upsilon(J_n(1))=b_n-1 for every n, including n=0,1,2, and since b_k>=1 for k>=1, Upsilon(J_(n-1)(1))<Upsilon(J_n(1))<Upsilon(J_(n+1)(1)) exactly when b_(n-1)<b_n<b_(n+1), for every n>=2. Theorem 2.3 of Kok and Susanth, arXiv:1410.8637v1, gives Upsilon(J_n(1)) as i-1 or i through the prime Jaconian vertex v_i for n>=3, and its page 5 conjectures the nonrepetition equivalence for n>=3; Kok, Linear Jaco Graphs: A Critical Review (2016), restates them as Theorem 2.48 and Conjecture 2.48.1 (not inspected), and Corollary 7 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24369124, derives Upsilon_n=b_n-1. The clique proof here is repo-derived.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var clique = All("L", Call("List", F.Id("V")), Iff(Equal(Call("run", F.Id("G"), F.Id("L")), F.Id("K")),
            Call("IsClique", F.Id("G"), Seq(F.OpenBrace, F.Id("v"), Colon, Sp, Call("notMem", F.Id("v"), F.Id("L")), F.CloseBrace))));
        var formula = All("n", Nat(), Equal(Ups(n), Subtract(B(n), D(1))));
        var prev = Subtract(n, D(1));
        var next = Add(n, D(1));
        var nonrep = All("n", Nat(), Imp(Le(D(2), n),
            Iff(And(Lt(Ups(prev), Ups(n)), Lt(Ups(n), Ups(next))), And(Lt(B(prev), B(n)), Lt(B(n), B(next))))));
        return Disp(And(clique, And(formula, nonrep)));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Ups(Formula n) => Call("Upsilon", Call("jaco", n));
    private static Formula B(Formula n) => Call("b", n);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
