using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class QuadripartiteH2ExactBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum triangular support after an edge repair equals the minimum total "
            + "four-coordinate Hamming cost of an unordered pairing of the tetrahedral defects.",
        H("Four-cube exact degree-two repair budget"),
        Blocks(
            Definition("cube-graph", "The dual cube", "cubeGraph",
                "Cube is Bool^4, represented by four Boolean coordinates. The fixed simple "
                    + "graph cubeGraph joins exactly the pairs at Hamming distance one. "
                    + "Face is Fin 4 times Bool^3 and indexes the actual unordered triangular "
                    + "faces of the boundary of the four-dimensional cross-polytope."),
            Definition("one-endpoint", "The positive endpoint of a dual edge", "insertOne",
                "insertOne(i,t) inserts true in coordinate i of the three-coordinate sign "
                    + "vector t. The existing insertZero inserts false in that coordinate."),
            Definition("dual-edge", "The actual face-to-edge map", "dualEdge",
                "dualEdge(f) is the unordered pair of insertZero(f.1,f.2) and "
                    + "insertOne(f.1,f.2). These two tetrahedra are incident to the face f."),
            Definition("support-edges", "Supported dual edges", "supportEdges",
                "For a binary triangular cochain F:Face -> ZMod 2, supportEdges(F) is "
                    + "the image under dualEdge of the nonzero faces. Its cardinality "
                    + "is exactly the support weight of F."),
            Definition("syndrome", "Tetrahedral defects", "syndrome",
                "syndrome(F) consists of the vertices b for which d2(F)(b) is nonzero. "
                    + "The tetrahedral defect d2(F)(b) sums the four incident triangular "
                    + "values in ZMod 2."),
            Definition("odd-terminals", "Odd terminals of a support", "oddTerminals",
                "oddTerminals(E) consists of the cube vertices incident to an odd "
                    + "number of edges of E. Incidences count each supported edge once."),
            Definition("path-piece", "A simple path piece", "PathPiece",
                "A PathPiece has two distinct cube endpoints and a walk in the fixed "
                    + "cube graph with no repeated vertices. It therefore repeats no edges."),
            Definition("cycle-piece", "A simple even cycle piece", "CyclePiece",
                "A CyclePiece is a nonempty closed trail in the fixed cube graph whose "
                    + "only repeated vertex is its base, together with evenness of its length."),
            Definition("support-certificate", "Exact support and terminal partition", "supportCertificate",
                "For finite E, a list ps of PathPiece values and a list cs of CyclePiece "
                    + "values form a supportCertificate when the concatenated path and "
                    + "cycle edge lists are a permutation of E.toList, the concatenated "
                    + "path endpoint lists are a permutation of oddTerminals(E).toList, "
                    + "the sum of all path and cycle lengths equals E.card, and the sum "
                    + "of endpoint Hamming distances is at most the sum of path lengths. "
                    + "The first permutation accounts for every edge exactly once, including "
                    + "all discarded cycles, and gives pairwise edge disjointness. The second "
                    + "permutation assigns each terminal exactly once. Paths may share vertices; "
                    + "a terminal may be internal to another path."),
            Definition("pair-cost", "Cost of one unordered pair", "pairCost",
                "pairCost is the four-coordinate Hamming distance lifted to Sym2 Cube. "
                    + "Symmetry makes this independent of an ordering of the two vertices."),
            Definition("pairing-cost", "Total pairing cost", "pairingCost",
                "pairingCost(P) sums pairCost over the finite list P. The empty list has cost zero."),
            Definition("pairing", "An unordered pairing", "IsPairing",
                "IsPairing(S,P) requires every Sym2 Cube value in P to be nondiagonal "
                    + "and the concatenation of their two-element vertex subsets to be "
                    + "a permutation of S.toList. Thus these unordered two-element subsets "
                    + "partition S, with every vertex appearing once. The order of the "
                    + "subsets carries no mathematical information."),
            Describe.Lean(
                DescribeId.Create("fourcube-exact-budget"),
                DeclarationHandle.Create(Prefix + "fourcube_exact_budget"),
                H("Exact support certificate and repair budget"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The face-to-edge map is injective and takes every actual "
                        + "triangle to a cube edge. Every finite cube edge support E has the full "
                        + "path and even-cycle certificate defined above. For every cochain F, "
                        + "supportEdges(F).card equals weight(F), and its odd terminals equal "
                        + "syndrome(F).")),
                    Paragraph(Text("For every binary triangular cochain F and every natural "
                        + "budget k, an edge cochain e with weight(F+d1(e)) <= k exists if and "
                        + "only if syndrome(F) has an unordered pairing P with pairingCost(P) "
                        + "<= k. This includes empty syndromes and k=0. The edge cochain uses "
                        + "the existing simplicial coboundary d1 on the actual triangular faces.")),
                    Paragraph(Text("Choose a globally longest trail in the remaining support. "
                        + "Its endpoints exhaust their incident support edges. If they differ, "
                        + "trail parity makes them odd terminals, and a simple path between them "
                        + "can be removed. If they agree, remove a nonempty simple cycle from "
                        + "the trail. The cube's Boolean coloring makes every closed walk even. "
                        + "Induction on the remaining support preserves the edge partition, "
                        + "the terminal partition, and the exact total length. The triangle "
                        + "inequality bounds endpoint Hamming costs by path lengths.")),
                    Paragraph(Text("For a repair, apply that certificate to the repaired "
                        + "support; d2(d1(e))=0 preserves the original syndrome. Conversely, "
                        + "sum the existing coordinate geodesics for the paired terminals. "
                        + "Their boundaries add to the syndrome and their weights sum to "
                        + "the pairing cost, with cancellation only reducing support. "
                        + "The existing universal repair theorem with p=2 and q=1, applied "
                        + "to F plus this filling with zero defect, supplies the edge cochain.")),
                    Paragraph(Text("The existing four-face antipodal path has weight four "
                        + "and two antipodal defects. Every edge repair still has weight "
                        + "at least four, as given by the existing octahedral sharpness theorem. "
                        + "The shortest-path parity mechanism is described by Edmonds and "
                        + "Johnson (1973), Section 3, pages 90-93. The support-count convention "
                        + "and coefficient-two bound are described by Dotterrer and Kahle, "
                        + "arXiv:1012.5316v2, Definitions 2.6 and 2.8 and Proposition 5.5."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Definition(string id, string title, string declaration,
        string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ResultFormula()
    {
        var cube = F.Id("Cube");
        var q = F.Id("cubeGraph");
        var f = F.Id("F");
        var e = F.Id("e");
        var k = F.Id("k");
        var p = F.Id("P");
        var support = F.Id("E");
        var edges = Call("edgeSet", q);
        var pairList = Call("List", Call("Sym2", cube));
        var injection = Call("Injective", F.Id("dualEdge"));
        var actualEdges = All("f", F.Id("Face"),
            Rel(Call("dualEdge", F.Id("f")), FormulaRelationOperator.MemberOf, edges));
        var certificate = All("E", Call("Finset", Call("Sym2", cube)),
            Logic(Rel(support, FormulaRelationOperator.SubsetOf, edges),
                FormulaLogicOperator.Implies,
                Exists("ps", Call("List", F.Id("PathPiece")),
                    Exists("cs", Call("List", F.Id("CyclePiece")),
                        Call("supportCertificate", support, F.Id("ps"), F.Id("cs"))))));
        var supportLaw = All("F", F.Id("Cochain"), And(
            Rel(Call("card", Call("supportEdges", f)), FormulaRelationOperator.Equal,
                Call("weight", f)),
            Rel(Call("oddTerminals", Call("supportEdges", f)), FormulaRelationOperator.Equal,
                Call("syndrome", f))));
        var repair = Exists("e", F.Id("EdgeCochain"),
            Rel(Call("weight", Add(f, Call("d1", e))), FormulaRelationOperator.LessThanOrEqual, k));
        var pairing = Exists("P", pairList, And(Call("IsPairing", Call("syndrome", f), p),
            Rel(Call("pairingCost", p), FormulaRelationOperator.LessThanOrEqual, k)));
        var budget = All("F", F.Id("Cochain"), All("k", F.Id("Nat"),
            Logic(repair, FormulaLogicOperator.Iff, pairing)));
        var sharpness = All("e", F.Id("EdgeCochain"),
            Rel(F.D(4), FormulaRelationOperator.LessThanOrEqual,
                Call("weight", Add(F.Id("path"), Call("d1", e)))));
        return F.Disp(And(injection, And(actualEdges,
            And(certificate, And(supportLaw, And(budget, sharpness))))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { F.Id(name), F.Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i != 0) items.Add(F.Comma);
            items.Add(arguments[i]);
        }
        items.Add(F.Close);
        return F.Seq([.. items]);
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Par(Formula formula) => F.Seq(F.Open, formula, F.Close);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Par(left), op, Par(right));
    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) => F.Seq(left, F.Plus, right);
}
