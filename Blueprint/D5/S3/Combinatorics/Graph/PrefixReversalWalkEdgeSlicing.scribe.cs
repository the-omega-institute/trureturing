using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class PrefixReversalWalkEdgeSlicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversalWalkEdgeSlicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting a nonempty collection of actual Hamilton cycle edges yields exactly one path per deleted edge, with every vertex occurring once.",
        H("Cutting Actual Graph Walks into Paths"),
        Blocks(
            Paragraph(Text(
                "Let G be a simple graph on a type V with decidable equality. A Piece(G) records two "
                + "endpoints and an actual G-walk between them. For a list L of pieces, flatMapSupport(L) "
                + "concatenates their full vertex-support lists, and flatMapEdges(L) concatenates their "
                + "undirected edge lists. Edges have type Sym2(V), so their orientation is forgotten. "
                + "The operator filterIn retains the list occurrences belonging to a finite edge set E; "
                + "filterOut retains the occurrences outside E.")),
            Describe.Lean(DescribeId.Create("path-edge-slicing"),
                DeclarationHandle.Create(Prefix + "exists_path_edge_slicing"),
                H("Literal Support and Edge Lists after Cutting a Path"),
                StatementSource.FromAuthor(PathFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Any path p and finite set E of undirected edges admit a list of actual path pieces. "
                        + "Their concatenated supports equal p's support in its original order. Their "
                        + "concatenated edges equal p's edge list with every selected occurrence removed. "
                        + "There is one more piece than selected edge occurrences. Edges of E that never "
                        + "occur in p cause no cut.")),
                    Paragraph(Text(
                        "The construction follows the actual walk from its first edge. A selected next "
                        + "edge ends the current piece and starts the next piece at its other endpoint. "
                        + "An unselected edge extends the current piece. Consecutive cuts therefore keep "
                        + "a nil walk at their common vertex; this piece has one vertex and no edges. "
                        + "Induction on the walk proves the support, edge-list and length identities, "
                        + "while the original path condition ensures every piece is a path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cycle-edge-slicing"),
                DeclarationHandle.Create(Prefix + "exists_cycle_edge_slicing"),
                H("Exactly One Actual Path per Selected Hamilton Cycle Edge"),
                StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume V is finite, p is an actual Hamilton cycle, and E is a nonempty finite "
                        + "set whose edges all belong to p's edge set. Then exactly |E| actual path pieces "
                        + "remain. Across their full supports, every vertex occurs exactly once. An "
                        + "undirected edge occurs among their edges exactly when it belongs to the "
                        + "original cycle and is outside E. Adjacent selected edges are allowed.")),
                    Paragraph(Text(
                        "Choose an edge of E and rotate the actual cycle to one of its endpoints. "
                        + "At that endpoint the chosen edge leads either to the second vertex or to the "
                        + "penultimate vertex; reversing the cycle handles the second case. Removing "
                        + "the first edge opens the cycle into a Hamilton path whose edges are exactly "
                        + "the original cycle edges except that chosen edge. Cutting this path removes "
                        + "the remaining selected edges. Its edge list has no repetitions, so the "
                        + "number of remaining selected occurrences is |E|-1. The path construction "
                        + "then gives |E| pieces and preserves every vertex once."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "These results concern a supplied actual path or Hamilton cycle and actual selected "
                + "edges. For prefix-reversal constructions, one must additionally prove that the "
                + "chosen native generator edges belong to that cycle and establish the endpoint "
                + "orientations needed to join the resulting pieces.")))));

    private static Formula PathFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), e = F.Id("E"), p = F.Id("p");
        Formula start = F.Id("start"), finish = F.Id("finish"), pieces = F.Id("L");
        Formula conclusion = Some("L", Call("List", Call("Piece", g)),
            And(PiecePaths(g, pieces),
                And(Equal(Call("flatMapSupport", pieces), Call("support", p)),
                    And(Equal(Call("flatMapEdges", pieces), Call("filterOut", e, Call("edges", p))),
                        Equal(Call("length", pieces), Add(Call("length", Call("filterIn", e, Call("edges", p))), D(1)))))));
        return Disp(All("V", Call("Type"), Seq(
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), All("E", Call("Finset", Call("Sym2", v)),
                All("start", v, All("finish", v, All("p", Call("Walk", g, start, finish),
                    Implies(Call("IsPath", p), conclusion)))))))));
    }

    private static Formula CycleFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), e = F.Id("E"), p = F.Id("p");
        Formula a = F.Id("a"), pieces = F.Id("L"), edge = F.Id("e");
        Formula genuineCuts = All("e", Call("Sym2", v),
            Implies(Member(edge, e), Member(edge, Call("edgeSet", p))));
        Formula supportOnce = All("v", v,
            Equal(Call("count", F.Id("v"), Call("flatMapSupport", pieces)), D(1)));
        Formula remainingEdges = All("e", Call("Sym2", v),
            Logic(Member(edge, Call("flatMapEdges", pieces)), FormulaLogicOperator.Iff,
                And(Member(edge, Call("edgeSet", p)), Call("Not", Member(edge, e)))));
        Formula conclusion = Some("L", Call("List", Call("Piece", g)),
            And(PiecePaths(g, pieces), And(supportOnce,
                And(remainingEdges, Equal(Call("length", pieces), Call("card", e))))));
        return Disp(All("V", Call("Type"), Seq(
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), All("E", Call("Finset", Call("Sym2", v)),
                All("a", v, All("p", Call("Walk", g, a, a),
                    Implies(And(Call("IsHamiltonianCycle", p), And(Call("Nonempty", e), genuineCuts)),
                        conclusion))))))));
    }

    private static Formula PiecePaths(Formula g, Formula pieces) =>
        All("z", Call("Piece", g), Implies(Member(F.Id("z"), pieces), Call("IsPath", Call("walk", F.Id("z")))));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
}
