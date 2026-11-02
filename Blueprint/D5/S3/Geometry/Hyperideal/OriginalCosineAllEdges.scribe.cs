using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class OriginalCosineAllEdgesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/Hyperideal/OriginalCosineAllEdges.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six target-edge original cosine bounds share one determinant sign.",
        H("Six original cosine bounds"),
        Blocks(
            Paragraph(Text("Fix the local edge order (12,13,14,34,24,23) and six coordinates (r,a,b,o,c,d), all greater than one. For one ordered tuple, strictCosine is the conjunction -1 < N/(sqrt(D1*D2)) and N/(sqrt(D1*D2)) < 1. The six target tuples are (r,a,b,o,c,d), (a,r,b,c,o,d), (b,r,a,d,o,c), (o,a,d,r,c,b), (c,r,d,a,o,b), and (d,r,c,b,o,a).")),
            Paragraph(Text("The determinant identity for each tuple is the existing OriginalCosineDeterminantInterface identity. The corresponding vertex relabeling simultaneously permutes rows and columns, so every transformed gram determinant equals the original determinant. Positivity of D1 and D2 follows from the six coordinates being greater than one; the square-root interval calculation is carried out over the reals.")),
            Paragraph(Text("This module closes the finite algebraic six-edge criterion only. It does not assert a hyperideal geometric realization, a compatible global face pairing, or any statement about the unresolved transport and gluing clauses.")),
            Node("all-edges-strict-iff-det-neg", "Common determinant criterion", "all_edges_strict_iff_det_neg", Statement(),
                "The common signed Gram determinant is negative exactly when all six target-edge original cosines lie strictly between -1 and 1."))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(F.Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula Statement()
    {
        var r = F.Id("r"); var a = F.Id("a"); var b = F.Id("b");
        var o = F.Id("o"); var c = F.Id("c"); var d = F.Id("d");
        var xs = new[] { r, a, b, o, c, d };
        var det = Call("det", Call("gram", xs));
        var cs = new[] {
            Call("strictCosine", r, a, b, o, c, d),
            Call("strictCosine", a, r, b, c, o, d),
            Call("strictCosine", b, r, a, d, o, c),
            Call("strictCosine", o, a, d, r, c, b),
            Call("strictCosine", c, r, d, a, o, b),
            Call("strictCosine", d, r, c, b, o, a)
        };
        Formula rhs = cs[0];
        for (var i = 1; i < cs.Length; i++) rhs = new Formula.Logic(rhs, FormulaLogicOperator.And, cs[i]);
        var hypotheses = new[] { r, a, b, o, c, d }
            .Select(x => Lt(F.D(1), x))
            .Aggregate((x, y) => new Formula.Logic(x, FormulaLogicOperator.And, y));
        var detNeg = new Formula.Relation(det, FormulaRelationOperator.LessThan, F.D(0));
        return Implies(hypotheses, new Formula.Logic(detNeg, FormulaLogicOperator.Iff, rhs));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
}
