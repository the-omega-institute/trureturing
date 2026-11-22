using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.TriangleRegularity;

internal sealed class SheffieldXiConjectureOneDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/sheffieldxi2025triangle");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The icosahedron has five neighbors and five induced edges at every vertex. No abelian Cayley graph has both local counts.",
        H("Sheffield–Xi Conjecture 1 and its refutation"),
        Blocks(
            Describe.Lean(DescribeId.Create("sheffield-xi-triangle-regular"),
                DeclarationHandle.Create(Prefix + "triangleRegular"),
                H("Triangle regularity"), StatementSource.FromAuthor(Disp(TriangleRegular())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The two counts use Nat.card on the open neighborhood and on the unordered edge set of its induced simple graph. On finite graphs, every vertex has degree r and its open neighborhood induces c edges. For arbitrary vertex types, Nat.card gives the usual size of each finite set and gives zero on each infinite set. An infinite neighborhood therefore contributes zero to the first count, and the second count is computed separately from its induced edge set."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sheffield-xi-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Abelian Cayley realization"), StatementSource.FromAuthor(Disp(Claim())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 1 asks for an abelian Cayley realization of every pair realized by a finite nonempty simple graph. The finite abelian group may have any order. Its connection set is closed under additive inversion and excludes zero. The chosen group structure instB determines both the Cayley adjacency and inversion on B. The display writes the anonymous Finite and Nonempty witnesses as conjunctions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sheffield-xi-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The icosahedral counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(Claim())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Use the icosahedral graph on two poles and two rings of five vertices. Every open neighborhood has five vertices and five edges. Caro and Mifsud give a twelve-vertex planar (5,5)-realization in Figure 5. Hak and coauthors identify the icosahedron as their graph G1 in Appendix A.")),
                    Paragraph(Text("In an abelian Cayley graph, the open neighborhood of zero is the connection set. Each oriented edge from x to y there corresponds to the ordered zero-sum triple (x, y − x, −y). Five unordered edges would give ten triples. Rotation counts those triples modulo three by their diagonal fixed points. Negation pairs the nonzero connection elements killed by three. In a five-element connection set the two congruences force exactly four such elements.")),
                    Paragraph(Text("The remaining element equals its negative and cannot occur in a zero-sum triple. Among the four elements killed by three, a repeated coordinate forces all three coordinates to agree. Three distinct coordinates cannot contain an opposite pair, since the third coordinate would then be zero. The four elements form two opposite pairs, so three distinct coordinates would have to contain such a pair. Only the four diagonal triples remain, contradicting the count of ten."))),
                DescribeRole.Theorem)), []));

    private static Formula TriangleRegular()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var vertex = F.Id("v");
        var r = F.Id("r");
        var c = F.Id("c");
        var neighbors = Call("SimpleGraph.neighborSet", graph, vertex);
        var edges = Call("SimpleGraph.edgeSet", Call("SimpleGraph.induce", graph, neighbors));
        return Seq(Forall, Sp, Typed(vertices, F.Id("Type")), Sp,
            Typed(graph, Call("SimpleGraph", vertices)), Sp, Typed(Seq(r, Sp, c), Nats()),
            Comma, Sp, Call("triangleRegular", graph, r, c), Sp, Iff, Sp,
            Par(Bind(Forall, vertex, vertices,
                Seq(Equal(Call("Nat.card", neighbors), r), Sp, Land, Sp,
                    Equal(Call("Nat.card", edges), c)))));
    }

    private static Formula Claim()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var group = F.Id("B");
        var groupInstance = F.Id("instB");
        var connection = F.Id("S");
        var x = F.Id("x");
        var r = F.Id("r");
        var c = F.Id("c");
        var graphSide = Bind(Exists, vertices, F.Id("Type"),
            Seq(Call("Finite", vertices), Sp, Land, Sp, Call("Nonempty", vertices), Sp, Land, Sp,
                Par(Bind(Exists, graph, Call("SimpleGraph", vertices),
                    Call("triangleRegular", graph, r, c)))));
        var connectionSide = Bind(Exists, connection, Call("Set", group),
            Seq(new Formula.Not(Par(Member(D(0), connection))), Sp, Land, Sp,
                Par(Bind(Forall, x, group, Seq(Member(x, connection), Sp, Implies, Sp,
                    Member(Seq(Minus, x), connection)))), Sp, Land, Sp,
                Call("triangleRegular", Call("SimpleGraph.addCayley", connection), r, c)));
        var groupStructure = Call("AddCommGroup", group);
        var cayleySide = Bind(Exists, group, F.Id("Type"),
            Seq(Call("Finite", group), Sp, Land, Sp,
                Par(Bind(Exists, groupInstance, groupStructure,
                    Seq(Operatorname, Grp(F.Id("letI")), Sp, Colon, Sp, groupStructure, Sp,
                        Colon, Eq, Sp, groupInstance, Semi, Sp, connectionSide)))));
        return Bind(Forall, Seq(r, Sp, c), Nats(),
            Seq(Par(graphSide), Sp, Implies, Sp, Par(cayleySide)));
    }

    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula name, Formula type) =>
        Par(Seq(name, Sp, Colon, Sp, type));
    private static Formula Bind(Formula quantifier, Formula name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Member(Formula item, Formula collection) =>
        new Formula.Relation(item, FormulaRelationOperator.MemberOf, collection);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0)
                parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return new Formula.Apply(Seq(Operatorname, Grp(Seq([.. parts]))), [.. arguments]);
    }
}
