using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class GurvichLeafRootEdgeDeletionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/GurvichLeafRootEdgeDeletionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gurvich2026noninduced");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting the edge at the first root of an inherent six-vertex path leaves a two-rooted graph that a nine-vertex tree confines.",
        H("Deleting a leaf root edge can destroy inherence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gurvich-leaf-root-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 6.4"), StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The graphs are finite and simple. The roots are ordered and distinct, with the degree of the first at most the degree of the second. The first root has exactly one neighbor, u. Deleting the unordered edge between s and u keeps both roots and every vertex.")),
                    Paragraph(Text("A copy is an injective adjacency-preserving map. The host may have extra edges between its image vertices. An extension attaches two distinct vertices outside the entire image to the respective roots. Reachability takes place in the induced graph on the complement of that image. The endpoints in the formula denote the corresponding vertices of this induced graph. A copy with no extensions is avoidable. Inherence asks for one avoidable copy in every finite host that contains a copy. Finite labels include every finite order and permit disconnected hosts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gurvich-leaf-root-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The four-arm tree confines the deleted path"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take the path on vertices 0 through 5 in order. Its roots are 0 and 3, of degrees one and two. For the intact path, work in the connected component of any containing copy. The specialization of Lemma 3.4 chooses a maximal connected vertex set disjoint from some copy. Path shifts and reroutings give either a copy with no extension or a copy whose exterior neighbors at both roots lie in that connected set. In the latter case the set supplies a walk between the endpoints of every extension. Transporting the copy and the walks to the original host proves inherence.")),
                    Paragraph(Text("Delete edge 0–1. The host tree has center 0 and arms (0,1,2), (0,3,4), (0,5,6) and (0,7,8). The tuple (5,2,1,0,3,4) gives a copy of the deleted graph in pattern vertex order. In every copy the surviving four-edge path uses two full arms and places root 3 at the center. Root 0 lies on a third arm. Attach its other vertex at the first root and the midpoint of the fourth arm at the second root. The first endpoint is isolated in the graph induced outside the copy, so the two endpoints cannot be joined there. This applies to every copy of the deleted graph."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gurvich-krnc-milanic-vyalyi-2026-leaf-root-edge-deletion"),
                    ResolutionKind.Refuted))), []));

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), h = F.Id("H"), s = F.Id("s"), t = F.Id("t"), u = F.Id("u"), v = F.Id("v");
        var vertices = Call("Fin", n);
        var soleNeighbor = All("v", vertices,
            new Formula.Logic(Call("Adj", h, s, v), FormulaLogicOperator.Iff,
                new Formula.Relation(v, FormulaRelationOperator.Equal, u)));
        var degreeOrder = new Formula.Relation(Call("degree", h, s), FormulaRelationOperator.LessThanOrEqual,
            Call("degree", h, t));
        var differentRoots = new Formula.Relation(s, FormulaRelationOperator.NotEqual, t);
        var deleted = Call("deleteEdges", h, Seq(OpenBrace, new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id("Sym"), D(2), Dot, F.Id("mk")))), [s, u]), CloseBrace));
        var conclusion = Implies(Inherence(h, s, t), Inherence(deleted, s, t));
        var body = Implies(degreeOrder, Implies(differentRoots, Implies(soleNeighbor, conclusion)));
        return All("n", Naturals, All("H", Call("SimpleGraph", vertices),
            All("s", vertices, All("t", vertices, All("u", vertices, body)))));
    }

    private static Formula Inherence(Formula pattern, Formula firstRoot, Formula secondRoot)
    {
        Formula m = F.Id("m"), g = F.Id("G"), f = F.Id("f"), x = F.Id("x"), y = F.Id("y");
        var vertices = Call("Fin", m);
        var copy = Call("Copy", pattern, g);
        var range = Call("range", f);
        var complement = Seq(vertices, Sp, Setminus, Sp, range);
        var extension = And(Outside(x, range), And(Outside(y, range),
            And(new Formula.Relation(x, FormulaRelationOperator.NotEqual, y),
                And(Call("Adj", g, new Formula.Apply(f, [firstRoot]), x), Call("Adj", g, new Formula.Apply(f, [secondRoot]), y)))));
        var closure = Call("Reachable", Call("induce", g, complement), x, y);
        var avoidable = All("x", vertices, All("y", vertices, Implies(extension, closure)));
        return All("m", Naturals, All("G", Call("SimpleGraph", vertices),
            Implies(Call("Nonempty", copy), Bind(Exists, "f", copy, avoidable))));
    }

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Outside(Formula vertex, Formula range) =>
        new Formula.Not(new Formula.Relation(vertex, FormulaRelationOperator.MemberOf, range));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Implies, right);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) => Bind(Forall, name, type, body);
    private static Formula Bind(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Par(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
}
