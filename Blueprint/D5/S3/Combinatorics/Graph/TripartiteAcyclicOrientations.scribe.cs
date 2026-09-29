using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class TripartiteAcyclicOrientationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/muhlherr2026acyclic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For all m, n, p at least 1 that are not all odd, the complete tripartite graph K_{m,n,p} has a number of acyclic orientations congruent to 2 modulo 4, as conjectured by L. Mühlherr and G. Poullot (clause (4) of Conjecture 1 of arXiv:2609.02249). The number of acyclic orientations of a graph is its Tutte polynomial at (2, 0), the q = -1 point of the Potts model.",
        H("Acyclic orientations of complete tripartite graphs modulo 4"),
        Blocks(
            Node("orientation", "Orientations", OrientationFormula(),
                "A Boolean relation d on the vertices orients the simple graph G when every edge {a, b} carries exactly one of the arcs a to b and b to a, and no other pair carries an arc.",
                "IsOrientation", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The number of acyclic orientations", CountFormula(),
                "psi(G) is the number of acyclic orientations of G, counted as Boolean relations on the vertex set. Acyclicity is the repository's AcyclicEdge of the dependency-reachability order, applied to the arcs d(x, y) = true: no vertex is related to itself by the transitive closure of the arcs.",
                "acyclicOrientationCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Clause (4) of Conjecture 1", ClaimFormula(),
                "For all m, n, p at least 1 that are not all odd, the complete tripartite graph K_{m,n,p}, Mathlib's complete multipartite graph over the family i ↦ Fin([m, n, p](i)) indexed by Fin 3, that is with parts Fin m, Fin n and Fin p, in which two vertices are adjacent exactly when they lie in different parts, has psi congruent to 2 modulo 4.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of clause (4)", Disp(F.Id("claim")),
                "If two commuting involutions r and s of a finite set act without fixed points, and so does r s, the orbits have four elements and 4 divides the size of the set. For non-adjacent vertices u and v with the same neighbours and an edge avoiding both, take r the reversal of all arcs and s the swap of u and v on the acyclic orientations: r has no fixed point because the graph has an edge, and r s has none because it reverses the edge avoiding u and v, so the acyclic orientations not fixed by s number a multiple of 4. The orientations fixed by s are those that give v the arcs of u, and deleting v is a bijection from them onto the acyclic orientations of the graph without v: a directed cycle through v becomes a closed walk through u. Hence psi(G) and psi(G - v) agree modulo 4. In K_{m,n,p} two vertices of the same part are such twins, and one vertex from each of the other two parts gives an edge avoiding them; removing vertices this way ends at the triangle K_{1,1,1}, whose 8 orientations are 6 transitive ones and 2 cyclic ones. So psi(K_{m,n,p}) is congruent to 6, that is to 2, modulo 4, for all m, n, p at least 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("muhlherr-poullot-2026-tripartite-acyclic-orientations"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("tripartiteao-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Not(Formula value) => Seq(Neg, Parenthesized(value));
    private static Formula IsTrue(Formula value) => Equal(value, Named("true"));
    private static Formula IsFalse(Formula value) => Equal(value, Named("false"));

    private static Formula OrientationFormula()
    {
        Formula g = F.Id("G"), d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), v = F.Id("V");
        Formula body = Iff(IsTrue(Call("d", a, b)),
            And(Call("Adj", g, a, b), IsFalse(Call("d", b, a))));
        return Disp(Iff(Call("IsOrientation", g, d), All("a", v, All("b", v, body))));
    }

    private static Formula CountFormula()
    {
        Formula g = F.Id("G"), d = F.Id("d"), x = F.Id("x"), y = F.Id("y");
        Formula arc = Seq(Open, Open, x, Comma, Sp, y, Close, Sp, Mapsto, Sp,
            IsTrue(Call("d", x, y)), Close);
        Formula set = Seq(OpenBrace, d, Colon, Sp, F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp,
            Named("Bool"), Sp, Mid, Sp,
            And(Call("IsOrientation", g, d), Call("AcyclicEdge", arc)), CloseBrace);
        return Disp(Equal(Call("acyclicOrientationCount", g), new Formula.Absolute(set)));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), p = F.Id("p");
        Formula i = F.Id("i");
        Formula entry = Seq(OpenBracket, m, Comma, Sp, n, Comma, Sp, p, CloseBracket, Open, i, Close);
        Formula parts = Seq(Open, Open, i, Sp, Colon, Sp, Call("Fin", D(3)), Close, Sp, Mapsto, Sp,
            Call("Fin", entry), Close);
        Formula tripartite = Call("completeMultipartiteGraph", parts);
        Formula notAllOdd = Not(And(Call("Odd", m), And(Call("Odd", n), Call("Odd", p))));
        Formula conclusion = Equal(Seq(Call("acyclicOrientationCount", tripartite), Sp, Named("mod"),
            Sp, D(4)), D(2));
        Formula body = Implies(AtMost(D(1), m), Implies(AtMost(D(1), n), Implies(AtMost(D(1), p),
            Implies(notAllOdd, conclusion))));
        return Disp(Iff(F.Id("claim"),
            All("m", Naturals(), All("n", Naturals(), All("p", Naturals(), body)))));
    }
}
