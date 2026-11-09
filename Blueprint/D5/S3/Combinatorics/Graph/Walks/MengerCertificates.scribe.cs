using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class MengerCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/MengerCertificates.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite vertex separators attain disjoint path certificates, with sharp weak duality for arbitrary walks.",
        H("Finite set-form Menger certificates"),
        Blocks(
            Describe.Lean(DescribeId.Create("separates"), DeclarationHandle.Create(Prefix + "Separates"),
                H("Separation by full walk support"), StatementSource.FromAuthor(SeparatorFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Separates(G,A,B,X) means that every G-walk starting in A and ending in B has a vertex in X in its support. Support includes both endpoints. There is no restriction that X avoid A or B."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("certificates-and-duality"),
                DeclarationHandle.Create(Prefix + "exists_separator_paths_and_weak_duality"),
                H("An attained certificate and universal walk weak duality"),
                StatementSource.FromAuthor(MainFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every vertex type V in any universe with Finite(V), every simple undirected graph G on V, and arbitrary finite vertex sets A and B, there is a finite separator X and an indexed family of exactly card(X) paths with initial vertices in A, final vertices in B, and pairwise disjoint full vertex supports. The same G, A and B satisfy the universal second clause: every finite separator Y bounds the size m of every pairwise vertex-disjoint family of A-to-B walks. The latter walks need not be paths.")),
                    Paragraph(Text("In the displayed formula, Fin(n) is the index type with n elements, a and b are functions from this index type to V, and WalkFamily(G,a,b) is the dependent product of G.Walk(a(i),b(i)) over that index type. The product contains actual walks, including nil walks. IsPath is required only for the attained certificate. Disjointness quantifies over every vertex of each support, including endpoints.")),
                    Paragraph(Text("Empty V, empty terminal sets, overlapping A and B, endpoint separators and zero-length paths remain in scope. In particular, the edge-free induction base uses nil paths at A intersect B. There is no connectedness, terminal-disjointness, distinct-terminal, nonadjacency or positive-length assumption. Directed, infinite-vertex, edge-disjoint and special two-terminal variants are outside this statement.")),
                    Paragraph(Text("The proof is received from Juan Pablo Traverso Gianini's jtraverso/menger-hamiltonian at immutable commit 35c5f684f9bfbd244bd0999ce725623ab571adb6. The source attributes its edge-induction proof to the second proof of Diestel, Graph Theory, Theorem 3.3.1 (Boehme, Goering, Harant). The private induction preserves the stronger terminal-clean Fam invariant because the splice consumes it; only the public output forgets those extra cleanliness clauses. Weak duality chooses a separator vertex on each walk and proves that disjointness makes this choice injective. This is known mathematics with source proof attribution.")),
                    Paragraph(Text("The source copyright and full Apache license are retained in the Lean source and docs/reports/licenses/menger-hamiltonian-LICENSE.txt. Retire this port when this repository's own pinned Mathlib supplies an equivalent entire finite set-form certificate and arbitrary-walk duality, after lawful migration of all consumers to direct applications."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V => F.Id("V");
    private static Formula G => F.Id("G");
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula X => F.Id("X");
    private static Formula Y => F.Id("Y");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula Vertex => F.Id("x");
    private static Formula SetV => Call("Finset", V);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula At(string f, Formula i) => Call(f, i);
    private static Formula Supp(Formula i) => Call("support", At("p", i));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Common(Formula body) => All("V", Call("Type"),
        Imp(Call("Finite", V), All("G", Call("SimpleGraph", V),
            All("A", SetV, All("B", SetV, body)))));
    private static Formula Sep(Formula s) => Call("Separates", G, A, B, s);
    private static Formula Walks => Call("WalkFamily", G, F.Id("a"), F.Id("b"));

    private static Formula SeparatorFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var p = F.Id("p");
        var body = All("a", V, Imp(Member(a, A), All("b", V, Imp(Member(b, B),
            All("p", Call("Walk", G, a, b), Ex("x", V,
                And(Member(Vertex, X), Member(Vertex, Call("support", p)))))))));
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", V),
            All("A", SetV, All("B", SetV, All("X", SetV, Iff(Sep(X), body)))))));
    }

    private static Formula Disjoint(Formula n) => All("i", Fin(n), All("j", Fin(n),
        Imp(Ne(I, J), All("x", V, Imp(Member(Vertex, Supp(I)),
            new Formula.Not(Member(Vertex, Supp(J))))))));

    private static Formula MainFormula()
    {
        var k = Card(X); var m = F.Id("m");
        var certificate = Ex("X", SetV, And(Sep(X),
            Ex("a", Arrow(Fin(k), V), Ex("b", Arrow(Fin(k), V), Ex("p", Walks,
                And(All("i", Fin(k), And(Member(At("a", I), A), Member(At("b", I), B),
                    Call("IsPath", At("p", I)))), Disjoint(k)))))));
        var duality = All("Y", SetV, Imp(Sep(Y), All("m", Call("Nat"),
            All("a", Arrow(Fin(m), V), All("b", Arrow(Fin(m), V), All("p", Walks,
                Imp(All("i", Fin(m), Member(At("a", I), A)),
                    Imp(All("i", Fin(m), Member(At("b", I), B)),
                        Imp(Disjoint(m), Le(m, Card(Y)))))))))));
        return Disp(Common(And(certificate, duality)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0
            ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
}
