using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class BarkerMinimalGridEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual inclusion-minimal dominating subsets of the labelled open three-row grid admit an exact column-word encoding and a five-column private-witness criterion.",
        H("Actual subsets and five-column minimal domination"),
        Blocks(
            N("MinimalDominating", "Inclusion minimality", "Domination uses SimpleGraph.IsDominating and is required separately. Every proper finite subset must fail domination. No minimum-cardinality, total-domination, independence or symmetry condition is added."),
            N("Closed", "Closed neighbourhoods", "Closed G u v means u=v or G.Adj u v."),
            N("ClosedPrivate", "Existential private witnesses", "ClosedPrivate G S v z means z is closed-adjacent to v and every selected closed neighbour of z equals v. Witnesses are propositions and are never counted choices."),
            T("minimal_iff_closed_private", "Private-witness characterization", PrivateFormula(), "The proof uses the existing criticalVertices, privateNeighbors and selfCritical_no_selected_neighbor suppliers. The isolated-or-outside-private-neighbour characterization, under the domination premise, is published as Proposition 1 of Gangloff and Talon, arXiv:1906.10779v2, https://arxiv.org/abs/1906.10779. No novelty is claimed for that characterization. No external prose or proof code is transplanted.",
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Automata/gangloff2019dominating"))),
            N("grid", "The ordinary open grid", "Vertices are Fin 3 × Fin n; (r,c) represents the source label (r+1,c+1). Adjacency is exactly Nat.dist r s + Nat.dist c d = 1. The finite column type supplies open ends."),
            N("encode", "Read the masks", "Each column mask has one Boolean bit for each of the three labelled rows. The bit is true exactly when the actual vertex belongs to the subset."),
            N("decode", "Recover the subset", "The decoded subset contains precisely the vertices whose column-mask bit is true."),
            N("mem_decode", "Selected bits", "For every width n, word w and vertex v, membership v ∈ decode w is equivalent to w(v.column)(v.row)=true.", DescribeRole.Theorem),
            N("subsetWordEquiv", "One subset, one word", "Finset (Vertex n) and Word n are equivalent through mutually inverse encode and decode. No automorphisms or witness choices are identified."),
            N("padded", "Real empty versus absent", "A signed column in 0 ≤ c < n returns some mask; other coordinates return none. The present all-false mask differs from absence."),
            N("minimalSets", "The original family", "Filter every actual labelled vertex subset by MinimalDominating (grid n). The original family is defined before transport to words."),
            N("actualCount", "The source count", "actualCount n is the cardinality of minimalSets n. The requested generating series uses positive n and separately sets its constant coefficient to zero."),
            N("ValidWord", "Acceptance against the actual graph", "Acceptance means domination of decode w and an existential closed private witness for each selected vertex."),
            T("validWord_iff", "Exact acceptance", ValidFormula(), "Apply the general characterization to the independently defined actual decoded subset."),
            N("minimalWordEquiv", "Restrict the bijection", "Restrict subsetWordEquiv to the actual minimal dominating subsets and accepted words."),
            N("ColumnTest", "Five-column criterion", "Every centre vertex is closed-dominated. Every selected centre vertex has an actual closed-neighbour witness; uniqueness is tested among selected vertices at column distance at most two. Actual finite-grid vertex types exclude absent witnesses."),
            T("minimal_iff_column_tests", "Every real centre at every width", ColumnFormula(), "A witness is at column distance at most one, and every selected neighbour of it is at distance at most two by the natural-distance triangle inequality. This proves that the five-column restriction retains the complete proper-subset condition, including widths one and two."),
            Paragraph(Text("The actual subset family is the source of the count throughout the transfer construction. The column criterion supplies the local tests, and the subset-word equivalence preserves every labelled choice without counting existential witnesses."))),
        []));

    private static DocumentBlock N(string name, string title, string prose,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create("bmg-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static DocumentBlock T(string name, string title, Formula formula, string prose,
        AssessedProvenance? provenance = null) => Describe.Lean(
        DescribeId.Create("bmg-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula X(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula All(string v, Formula ty, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(v), Sp, Colon, Sp, ty)), Comma, Sp, body);
    private static Formula Ex(string v, Formula ty, Formula body) =>
        Seq(Exists, Sp, Par(Seq(X(v), Sp, Colon, Sp, ty)), Comma, Sp, body);
    private static Formula Rel(Formula l, FormulaRelationOperator op, Formula r) => new Formula.Relation(l, op, r);
    private static Formula Logic(Formula l, FormulaLogicOperator op, Formula r) => new Formula.Logic(Par(l), op, Par(r));
    private static Formula Iff(Formula l, Formula r) => Logic(l, FormulaLogicOperator.Iff, r);
    private static Formula And(Formula l, Formula r) => Logic(l, FormulaLogicOperator.And, r);
    private static Formula Imp(Formula l, Formula r) => Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula In(Formula l, Formula r) => Rel(l, FormulaRelationOperator.MemberOf, r);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Verts(Formula n) => Call("Vertex", n);
    private static Formula FS(Formula t) => Call("Finset", t);
    private static Formula PrivateFormula()
    {
        Formula v = X("V"), g = X("G"), s = X("S"), x = X("v"), z = X("z");
        Formula witnesses = All("v", v,
            Imp(In(x, s), Ex("z", v, Call("ClosedPrivate", g, s, x, z))));
        Formula characterization = Iff(Call("MinimalDominating", g, s),
            And(Call("IsDominating", g, s), witnesses));
        return All("V", X("Type"), Imp(Call("Finite", v),
            All("G", Call("SimpleGraph", v), All("S", FS(v), characterization))));
    }
    private static Formula ValidFormula()
    {
        Formula n = X("n"), w = X("w");
        return All("n", Nat, All("w", Call("Word", n), Iff(Call("ValidWord", w),
            Call("MinimalDominating", Call("grid", n), Call("decode", w)))));
    }
    private static Formula ColumnFormula()
    {
        Formula n = X("n"), s = X("S"), c = X("c");
        return All("n", Nat, All("S", FS(Verts(n)), Iff(Call("MinimalDominating", Call("grid", n), s),
            All("c", Call("Fin", n), Call("ColumnTest", s, c)))));
    }
}
