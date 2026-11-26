using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class ZhengWuOddLineTreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/zheng2025oddspanning");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd line-graph spanning trees are characterized by odd branches of an endpoint split tree.",
        H("Odd spanning trees of line graphs"),
        Blocks(
            Paragraph(DefinitionDsl.Text(
                "The root graph is finite, undirected and simple. Its line graph has the root edges as vertices. A spanning tree is connected and acyclic on that entire vertex type, hence has a nonempty vertex set.")),
            Describe.Lean(
                DescribeId.Create("zheng-wu-odd-line-tree"),
                DeclarationHandle.Create(Owner + "result"),
                H("The endpoint partition criterion"),
                StatementSource.FromAuthor(Criterion()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(DefinitionDsl.Text(
                        "A partition P assigns nonempty classes of incident edges at each root vertex. A class bears its root vertex as a tag. T(P) joins the classes of each root edge at its two endpoints, one edge per root edge. An isolated root vertex contributes no classes. A branch at b is a connected component of the induced graph on all vertices of T(P) other than b, and its order is the cardinality of its support.")),
                    Paragraph(DefinitionDsl.Text(
                        "The equivalence holds for disconnected roots and roots with isolates. Both sides fail when the root edge count is zero or odd. The two-odd-branch requirement applies exactly at vertices of T(P) with at least two neighbors.")),
                    Paragraph(DefinitionDsl.Text(
                        "In the forward direction, restrict the spanning tree to the incident edges at each root vertex. The connected components of the resulting forests define the blocks. Each line-tree edge belongs to a unique forest. The block graph is connected, and subtracting the local tree sizes shows that a block graph with m edges has m + 1 vertices.")),
                    Paragraph(DefinitionDsl.Text(
                        "The sum of the degrees contributed by the two endpoint blocks to each line-tree vertex is odd. Orient its root edge toward the block making the odd contribution. Each local tree has an even number of odd-degree vertices, so every block has even indegree. The cut count identifies the incoming edges with the odd-order branches. A local tree on at least two vertices has at least two odd-degree vertices.")),
                    Paragraph(DefinitionDsl.Text(
                        "Conversely, the odd branches specify the even-indegree orientation of T(P). At each block choose a tree with exactly its incoming members of odd degree. A singleton uses the one-vertex tree. For larger blocks the incoming set is nonempty and even, and a path with leaves attached realizes the prescribed set. Join the local trees on their original edge labels. The union is connected, has m − 1 edges, and gives every original edge exactly one odd local contribution."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zheng-wu-2025-odd-line-spanning-trees"), ResolutionKind.Proved)))));

    private static Formula Criterion()
    {
        var vertices = F.Id("V");
        var root = F.Id("F");
        var tree = F.Id("H");
        var edge = F.Id("e");
        var partitions = F.Id("P");
        var block = F.Id("b");
        var branch = F.Id("C");
        var edges = ApplyName("E", root);
        var split = ApplyName("T", partitions);
        var withoutBlock = new Formula.Binary(split, FormulaBinaryOperator.Subtract, block);
        var oddBranches = Seq(OpenBrace, Sp, branch, Sp, Colon, Sp, ApplyName("Components", withoutBlock),
            Sp, Mid, Sp, ApplyName("Odd", Card(ApplyName("supp", branch))), Sp, CloseBrace);
        var lhs = Bind(Exists, tree, ApplyName("SimpleGraph", edges), And(
            LeqFormula(tree, ApplyName("L", root)), And(ApplyName("IsTree", tree),
                Bind(Forall, edge, edges, ApplyName("Odd", Card(ApplyName("N", tree, edge)))))));
        var rhs = And(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, Card(edges)),
            And(ApplyName("Even", Card(edges)), Bind(Exists, partitions, ApplyName("EndpointPartition", root),
                And(ApplyName("IsTree", split), Bind(Forall, block, ApplyName("Block", partitions),
                    Logic(LeqFormula(Num(2), Card(ApplyName("N", split, block))),
                        FormulaLogicOperator.Implies, LeqFormula(Num(2), Card(oddBranches))))))));
        return Disp(Bind(Forall, vertices, F.Id("Type"),
            Seq(OpenBracket, ApplyName("Finite", vertices), CloseBracket, Comma, Sp,
                Bind(Forall, root, ApplyName("SimpleGraph", vertices),
                    Logic(lhs, FormulaLogicOperator.Iff, rhs)))));
    }

    private static Formula ApplyName(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Bind(Formula quantifier, Formula name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Open, name, Sp, Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Card(Formula collection) => Seq(Lvert, Sp, collection, Sp, Rvert);

    private static Formula LeqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));

    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
}
