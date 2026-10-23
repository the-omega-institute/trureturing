using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class EdgeSlicingCutEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/EdgeSlicingCutEndpoints.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cutting actual selected Hamilton cycle edges preserves the actual cut-vertex endpoints of every remaining path.",
        H("Actual Endpoints of Hamilton Cycle Slices"),
        Blocks(Describe.Lean(DescribeId.Create("cycle-slicing-cut-endpoints"),
            DeclarationHandle.Create(Prefix + "exists_cycle_edge_slicing_with_cut_endpoints"),
            H("Every Slice Ends at Actual Selected Edges"),
            StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let G be a simple graph on a finite type V with decidable equality, p an actual "
                + "Hamilton cycle, and E a nonempty finite set of actual edges of p. The theorem "
                + "constructs exactly |E| simple path pieces. Their combined supports contain each "
                + "vertex exactly once, and their combined edge list contains precisely the actual "
                + "cycle edges outside E. In addition, the start and finish of every piece are "
                + "incident to edges of E. Adjacent cuts retain their common vertex as a nil piece.")),
                Paragraph(Text(
                "Open the original cycle at a selected actual edge using the frozen endpoint-aware "
                + "opening theorem. Induction over the remaining actual path proves that its first "
                + "piece can end only at the original finish or at a selected cut, and every later "
                + "piece starts at a selected cut and has the same finish alternative. The two "
                + "original endpoints belong to the opening cut. Combining these boundary laws "
                + "with the existing literal support, edge and length laws yields the endpoint "
                + "certificate without changing the retained vertex or edge inventory."))),
            DescribeRole.Theorem))));

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
        Formula z = F.Id("z"), boundaryEdge = F.Id("f");
        Formula CutVertex(Formula vertex) => Some("f", Call("Sym2", v),
            And(Member(boundaryEdge, e), Member(vertex, boundaryEdge)));
        Formula boundaries = All("z", Call("Piece", g), Implies(Member(z, pieces),
            And(CutVertex(Call("start", z)), CutVertex(Call("finish", z)))));
        Formula conclusion = Some("L", Call("List", Call("Piece", g)),
            And(PiecePaths(g, pieces), And(supportOnce,
                And(remainingEdges, And(Equal(Call("length", pieces), Call("card", e)), boundaries)))));
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
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
}
