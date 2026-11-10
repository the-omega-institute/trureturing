using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LocalConvexCombinationExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convexity of cosh excludes a local convex-combination flat candidate.",
        H("A local convex-combination obstruction"),
        Blocks(
            Paragraph(Text("For a finite coordinate space, q, q1 and q2 are reading vectors and ell is a real length vector. The dot product records the actual pair length mean. If q is a convex combination of q1 and q2 with coefficient lambda in the unit interval, the convexity of cosh bounds the potential at q by the corresponding weighted sum.")),
            Paragraph(Text("Each cosh value is positive. The weighted sum is therefore at most the unweighted sum of the two endpoint potentials, while the flat-candidate inequality requires one additional unit. These inequalities are incompatible.")),
            Describe.Lean(
                DescribeId.Create("local-convex-combination-exclusion"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/LocalConvexCombinationExclusion.local_convex_combination_exclusion"),
                H("Convex combinations cannot satisfy the flat candidate inequality"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof derives the dot-product relation from the vector equality, applies the two-point Jensen inequality for cosh, and then uses positivity together with the coefficient bounds to contradict the required unit gap.")),
                    Paragraph(Text("The statement applies to any finite real coordinate space and any real length vector. It records the local nonlinear obstruction only; it does not assert that every remaining acyclic candidate has a realization or that all low-degree candidates are eliminated."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var n = F.Id("n");
        var nat = F.Id("Nat");
        var real = F.Id("Real");
        var q = F.Id("q");
        var q1 = F.Id("q1");
        var q2 = F.Id("q2");
        var ell = F.Id("ell");
        var lambda = F.Id("lambda");
        var vector = Call("Function", Call("Fin", n), real);
        var dot1 = Call("dotProduct", q1, ell);
        var dot2 = Call("dotProduct", q2, ell);
        var dot = Call("dotProduct", q, ell);
        var qcomb = Call("add", Call("smul", lambda, q1),
            Call("smul", Seq(F.D(1), F.Minus, lambda), q2));
        var hypotheses = And(
            Le(F.D(0), lambda),
            Le(lambda, F.D(1)),
            Eq(q, qcomb),
            Le(Add(F.D(1), Add(Call("cosh", dot1), Call("cosh", dot2))), Call("cosh", dot)));
        return All("n", nat,
            All("q", vector,
                All("q1", vector,
                    All("q2", vector,
                        All("ell", vector,
                            All("lambda", real,
                                Imp(hypotheses, F.Id("False"))))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] parts)
    {
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        F.Seq(left, F.Plus, F.Sp, right);
    private static Formula Seq(params Formula[] parts) => F.Seq(parts);
}
