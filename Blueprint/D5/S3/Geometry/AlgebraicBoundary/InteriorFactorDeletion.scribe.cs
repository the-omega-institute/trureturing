using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class InteriorFactorDeletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting a linear factor through an interior point on the entire convex boundary.",
        H("Whole boundary factor deletion"),
        Blocks(
            Paragraph(Text("Let E be a real normed vector space, B a convex subset, and a an interior point of B. Let L be a nonzero continuous real linear functional and g a continuous real function on E. If L(x-a)g(x) vanishes at every boundary point of B, then g vanishes at every boundary point of B. Compactness, finite dimension and differentiability of the boundary are unnecessary for this implication.")),
            Describe.Lean(
                DescribeId.Create("whole-boundary-factor-delete"),
                DeclarationHandle.Create("D5/S3/Geometry/AlgebraicBoundary/InteriorFactorDeletion.whole_boundary_factor_delete"),
                H("A hyperplane through an interior point contributes no indispensable boundary factor"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Translate a to the origin and write mu for the convex gauge of B. The gauge is continuous and equals one exactly on the boundary. At a boundary point b with L(b)=0, choose v with L(v) nonzero. For all sufficiently small nonzero real t, mu(b+tv) is positive and z(t)=(b+tv)/mu(b+tv) belongs to the boundary. Its L value is nonzero, so g(z(t))=0. Since z(t) tends to b, continuity gives g(b)=0. At a boundary point with L(b) nonzero, cancellation gives the result directly. This argument also includes a one-dimensional ambient space.")),
                    Paragraph(Text("For a polynomial factorization f(x)=L(x-a)g(x), polynomial continuity supplies the hypothesis on g. Thus the factor can be deleted from an equation of the entire boundary. This implication does not assert the existence of that factorization, the nonvanishing of the derivative at an interior zero, a principal boundary ideal, or a hyperbolic branch representation."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var e = F.Id("E");
        var b = F.Id("B");
        var a = F.Id("a");
        var l = F.Id("L");
        var g = F.Id("g");
        var x = F.Id("x");
        var real = F.Id("Real");
        var boundary = Call("frontier", b);
        var vanishing = All("x", e, Imp(Member(x, boundary),
            Eq(Call("mul", Call("L", Call("sub", x, a)), Call("g", x)), F.D(0))));
        var conclusion = All("x", e, Imp(Member(x, boundary), Eq(Call("g", x), F.D(0))));
        var hypotheses = And(Call("Convex", real, b), Member(a, Call("interior", b)),
            Call("Nonzero", l), Call("Continuous", g), vanishing);
        var body = All("g", Call("Function", e, real), Imp(hypotheses, conclusion));
        body = All("L", Call("ContinuousLinearMap", real, e, real), body);
        body = All("a", e, body);
        body = All("B", Call("Set", e), body);
        return All("E", F.Id("RealNormedVectorSpace"), body);
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] parts)
    {
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
}
