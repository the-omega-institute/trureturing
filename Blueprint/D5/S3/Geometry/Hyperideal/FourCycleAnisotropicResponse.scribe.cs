using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleAnisotropicResponseDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleAnisotropicResponse.paired_angle_half_difference";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed transverse angle response for paired hyper-ideal lengths.",
        H("The transverse half-difference retains its sign"),
        Blocks(
            Paragraph(Text("Use the six cosine-length entries (r,a,b,o,a,b) in the "
                + "order (12,13,14,34,24,23). The target and both transverse "
                + "cosine entries lie strictly between -1 and 1.")),
            Describe.Lean(
                DescribeId.Create("paired-fourcycle-signed-half-difference"),
                DeclarationHandle.Create(Declaration),
                H("Exact half-difference response"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For r,a,b,o>1, let theta, beta and delta be the "
                        + "arccosine angles of the target and two transverse edges. "
                        + "Their signed half-difference is arctan of lambda-minus "
                        + "times cot(theta/2), where lambda-minus is the difference "
                        + "of the two positive transverse radicals divided by a+b "
                        + "and multiplied by sqrt((r-1)/(r+1)).")),
                    Paragraph(Text("The proof obtains the signed sine difference "
                        + "from both distinct cosine numerator-square factorizations. "
                        + "The half-difference lies in (-pi/2,pi/2), so the "
                        + "arctangent branch preserves its sign even when a<b.")),
                    Paragraph(Text("The statement uses only the displayed cosine "
                        + "formula and three angle-range premises. It does not "
                        + "certify a geometric tetrahedron, establish the "
                        + "half-sum response, or construct a global realization."))),
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
        var halfDifference = new Formula.Fraction(
            F.Seq(Call("arccos", ca), F.Minus, Call("arccos", cb)), F.D(2));
        var rootA = Call("sqrt", F.Seq(new Formula.Power(a, F.D(2)), F.Minus, F.D(1)));
        var rootB = Call("sqrt", F.Seq(new Formula.Power(b, F.D(2)), F.Minus, F.D(1)));
        var lambdaMinus = F.Seq(
            new Formula.Fraction(F.Seq(rootA, F.Minus, rootB), F.Seq(a, F.Plus, b)),
            F.Cdot, F.Sp,
            Call("sqrt", new Formula.Fraction(F.Seq(r, F.Minus, F.D(1)),
                F.Seq(r, F.Plus, F.D(1)))));
        var response = Call("arctan", F.Seq(lambdaMinus, F.Cdot, F.Sp,
            Call("cot", new Formula.Fraction(Call("arccos", ct), F.D(2)))));
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = [.. new[] { "r", "a", "b", "o" }
            .Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), real))];
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders],
            new Formula.Logic(premise, FormulaLogicOperator.Implies,
                new Formula.Relation(halfDifference, FormulaRelationOperator.Equal, response)));
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
