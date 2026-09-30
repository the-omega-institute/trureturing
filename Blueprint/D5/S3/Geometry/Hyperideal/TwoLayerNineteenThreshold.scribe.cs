using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class TwoLayerNineteenThresholdDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/TwoLayerNineteenThreshold.exact_uniform_two_layer_threshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact degree threshold for uniform two-layer angle bounds.",
        H("Uniform two-layer endpoint bounds"),
        Blocks(
            Paragraph(Text("Let b be the common low-edge upper bound and c the common "
                + "high-edge upper bound, with 1<b<=2 and 1<c<=b. The independent "
                + "opposite-edge endpoint is one. The low-edge and high-edge worst-case "
                + "cosines are L(b,c)=(2c^2-b+1)/(2c^2+b-1) and "
                + "H(b,c)=(2b^2-c+1)/(2b^2+c-1), respectively.")),
            Describe.Lean(
                DescribeId.Create("uniform-two-layer-below-nineteen-obstruction"),
                DeclarationHandle.Create(Declaration),
                H("The exact threshold"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If the low-edge angle arccos L(b,c) is strictly "
                        + "above pi/3, then H(b,c)>47/50. The three-angle cosine "
                        + "identity shows cos(pi/9)<47/50, so the high-edge angle "
                        + "is strictly below pi/9. For every positive integer D at "
                        + "most eighteen, pi/9 is no greater than 2pi/D. The two "
                        + "required strict angle inequalities therefore cannot "
                        + "hold together.")),
                    Paragraph(Text("At degree nineteen, b=2 and c=153/125 satisfy "
                        + "both strict conditions. The original six-coordinate "
                        + "endpoint cosines are 31193/62443 and 243/257. A rigorous "
                        + "sine remainder bound at 22/133 and a rational upper "
                        + "bound for pi show that arccos(243/257)>2pi/19.")),
                    Paragraph(Text("This exact threshold concerns the specified "
                        + "uniform two-layer endpoint estimate. It makes no "
                        + "assertion about other bound schemes or a hyperbolic "
                        + "realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var d = F.Id("D");
        var b = F.Id("b");
        var c = F.Id("c");
        var pi = F.Pi;
        var lowAngle = Call("arccos", Call("cosine", b, c, c, F.D(1), c, c));
        var highAngle = Call("arccos", Call("cosine", c, b, b, F.D(1), b, b));
        var premises = And(Lt(F.D(0), d), Le(d, F.D(1, 8)),
            Lt(F.D(1), b), Le(b, F.D(2)), Lt(F.D(1), c), Le(c, b));
        var lowTarget = Lt(new Formula.Fraction(pi, F.D(3)), lowAngle);
        var highTarget = Lt(new Formula.Fraction(Mul(F.D(2), pi), d), highAngle);
        var impossibleBelow = All([("D", F.Id("Nat")),
                ("b", F.Id("Real")), ("c", F.Id("Real"))],
            new Formula.Logic(premises, FormulaLogicOperator.Implies,
                new Formula.Not(And(lowTarget, highTarget))));
        var witness = Exists([("b", F.Id("Real")), ("c", F.Id("Real"))],
            And(Lt(F.D(1), b), Le(b, F.D(2)), Lt(F.D(1), c), Le(c, b),
                lowTarget,
                Lt(new Formula.Fraction(Mul(F.D(2), pi), F.D(1, 9)), highAngle)));
        return And(impossibleBelow, witness);
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula Exists((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [.. variables.Select(v => new Formula.BoundVariable(
                FormulaIdentifier.Create(v.Name), v.Type))], body);
    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mul(Formula left, Formula right) =>
        F.Seq(left, F.Cdot, F.Sp, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
