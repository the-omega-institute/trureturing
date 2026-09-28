using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleAnisotropicMeanResponseDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleAnisotropicMeanResponse.paired_angle_half_sum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mean transverse angle response for paired hyper-ideal lengths.",
        H("The transverse half-sum has an exact response"),
        Blocks(
            Paragraph(Text("Use the six cosine-length entries (r,a,b,o,a,b) in the "
                + "order (12,13,14,34,24,23). The target and both transverse "
                + "cosine entries lie strictly between -1 and 1.")),
            Describe.Lean(
                DescribeId.Create("paired-fourcycle-half-sum"),
                DeclarationHandle.Create(Declaration),
                H("Exact half-sum response"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For r,a,b,o>1, let theta, beta and delta be the "
                        + "arccosine angles of the target and two transverse edges. "
                        + "Their half-sum is arctan of lambda-plus times cot(theta/2), "
                        + "where lambda-plus is the sum of the two positive transverse "
                        + "radicals divided by a+b and multiplied by "
                        + "sqrt((r-1)/(r+1)).")),
                    Paragraph(Text("The two transverse numerator-square factorizations "
                        + "give the positive sine sum. Their cosine sum is positive, "
                        + "which places the mean angle in (0,pi/2) and fixes the "
                        + "arctangent branch.")),
                    Paragraph(Text("The statement uses only the displayed cosine "
                        + "formula and three angle-range premises. It does not "
                        + "certify a geometric tetrahedron, prove the parameter "
                        + "bounds, or construct a global realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = F.Id("r"); var a = F.Id("a");
        var b = F.Id("b"); var o = F.Id("o");
        var ct = Call("cosine", r, a, b, o, a, b);
        var ca = Call("cosine", a, b, r, a, b, o);
        var cb = Call("cosine", b, a, r, b, a, o);
        var premise = And(
            Lt(F.D(1), r), Lt(F.D(1), a), Lt(F.D(1), b), Lt(F.D(1), o),
            Lt(F.Seq(F.Minus, F.D(1)), ct), Lt(ct, F.D(1)),
            Lt(F.Seq(F.Minus, F.D(1)), ca), Lt(ca, F.D(1)),
            Lt(F.Seq(F.Minus, F.D(1)), cb), Lt(cb, F.D(1)));
        var halfSum = new Formula.Fraction(
            F.Seq(Call("arccos", ca), F.Plus, Call("arccos", cb)), F.D(2));
        var rootA = Call("sqrt", F.Seq(new Formula.Power(a, F.D(2)), F.Minus, F.D(1)));
        var rootB = Call("sqrt", F.Seq(new Formula.Power(b, F.D(2)), F.Minus, F.D(1)));
        var lambdaPlus = F.Seq(
            new Formula.Fraction(F.Seq(rootA, F.Plus, rootB), F.Seq(a, F.Plus, b)),
            F.Cdot, F.Sp,
            Call("sqrt", new Formula.Fraction(F.Seq(r, F.Minus, F.D(1)),
                F.Seq(r, F.Plus, F.D(1)))));
        var response = Call("arctan", F.Seq(lambdaPlus, F.Cdot, F.Sp,
            Call("cot", new Formula.Fraction(Call("arccos", ct), F.D(2)))));
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = [.. new[] { "r", "a", "b", "o" }
            .Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), real))];
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders],
            new Formula.Logic(premise, FormulaLogicOperator.Implies,
                new Formula.Relation(halfSum, FormulaRelationOperator.Equal, response)));
    }

    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction.");
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
