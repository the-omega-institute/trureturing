using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;
internal sealed class WignerSimplexNearestEdgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/WignerSimplexNearestEdge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit convex mixtures give the exact L1 error to the four-coordinate edge polytope.",
        H("Nearest point in the four-coordinate edge polytope"), Blocks(
            Describe.Lean(DescribeId.Create("wigner-edge-vertex"), DeclarationHandle.Create(Prefix + "edgeVertex"),
                H("Edge vertices"), StatementSource.FromAuthor(Disp(Vertex())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An edge vertex assigns one half to either endpoint and zero elsewhere."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wigner-free-edges"), DeclarationHandle.Create(Prefix + "freeEdges"),
                H("Distinct endpoint vertices"), StatementSource.FromAuthor(Disp(Edges())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("freeEdges consists of the vertices with two distinct endpoints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wigner-nearest-edge"), DeclarationHandle.Create(Prefix + "nearest_edge_point"),
                H("An attaining edge-polytope mixture"), StatementSource.FromAuthor(Disp(Nearest())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the minimum is nonnegative, five explicit nonnegative coefficients express the vector as an edge mixture. Otherwise transfer its negative minimum to a maximum coordinate. The corrected vector lies in a triangular face, and its L1 error is the original L1 norm minus one. Pair bounds, uniqueness of a negative entry and the minimum cap are explicit hypotheses."))), DescribeRole.Theorem))));
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string s, Formula t, Formula x) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, x);
    private static Formula Ex(string s, Formula t, Formula x) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, x);
    private static Formula At(Formula f, Formula a) => new Formula.Apply(f, [a]);
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin() => Call("Fin", D(4));
    private static Formula Vec() => new Formula.TypeArrow(Fin(), Real());
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula W(string i) => At(V("w"), V(i));
    private static Formula Norm(Formula x) => Call("norm", Call("toLp", D(1), x));
    private static Formula Vertex() => All("i", Fin(), All("j", Fin(), All("k", Fin(),
        Equal(At(Call("edgeVertex", V("i"), V("j")), V("k")),
            Call("ite", Or(Equal(V("k"), V("i")), Equal(V("k"), V("j"))), new Formula.Fraction(D(1), D(2)), D(0))))));
    private static Formula Edges() => All("w", Vec(), Iff(Mem(V("w"), V("freeEdges")),
        Ex("i", Fin(), Ex("j", Fin(), And(Ne(V("i"), V("j")), Equal(V("w"), Call("edgeVertex", V("i"), V("j"))))))));
    private static Formula Nearest()
    {
        var sum = Seq(Sum, Underscore, Grp(V("i"), Colon, Fin()), Sp, W("i"));
        var pair = All("i", Fin(), All("l", Fin(), Imp(Ne(V("i"), V("l")),
            And(Le(D(0), Add(W("i"), W("l"))), Le(Add(W("i"), W("l")), D(1))))));
        var unique = All("i", Fin(), All("l", Fin(), Imp(Lt(W("i"), D(0)), Imp(Lt(W("l"), D(0)), Equal(V("i"), V("l"))))));
        var conclusion = Ex("f", Vec(), And(Mem(V("f"), Call("convexHull", Real(), V("freeEdges"))),
            Equal(Norm(Par(Subtract(V("w"), V("f")))), Subtract(Norm(V("w")), D(1)))));
        return All("w", Vec(), All("j", Fin(), All("k", Fin(), Imp(Equal(sum, D(1)),
            Imp(All("i", Fin(), Le(W("j"), W("i"))), Imp(All("i", Fin(), Le(W("i"), W("k"))),
                Imp(pair, Imp(unique, Imp(All("i", Fin(), Le(Add(W("i"), W("j")), new Formula.Fraction(D(1), D(2)))), conclusion)))))))));
    }
}
