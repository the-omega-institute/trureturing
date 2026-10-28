using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class IndependentEndpointBarrierDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/IndependentEndpointBarrier.independent_endpoint_certificate_fails";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent opposite-edge endpoint certificates cannot close degree-eight or degree-nine stars.",
        H("Independent opposite-edge endpoint barrier"),
        Blocks(
            Paragraph(Text("The endpoint certificate fixes the opposite coordinate at one and "
                + "uses neighboring coordinates in [b,2], where 1<b<=2. The result is a "
                + "local analytic obstruction and does not claim that every corresponding "
                + "triangulation lacks a geometric realization.")),
            Describe.Lean(
                DescribeId.Create("independent-endpoint-certificate-obstruction"),
                DeclarationHandle.Create(Declaration),
                H("The endpoint certificate obstruction"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The all-b endpoint has cosine "
                        + "(2*b^3+b^2+1)/(2*b^3+3*b^2-1), whose exact difference from "
                        + "7/9 is 4*(b-2)^2*(b+1)/(9*(2*b^3+3*b^2-1)). Mixed-coordinate "
                        + "monotonicity and cos(2*pi/9)<7/9 give theta<2*pi/9.")),
                    Paragraph(Text("Consequently both 8*theta and 9*theta are strictly less "
                        + "than 2*pi. The statement applies only to the independent "
                        + "opposite-edge endpoint certificate; it preserves possible "
                        + "positive lower bounds and other length correlations."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var b = F.Id("b");
        var y = F.Id("y");
        var z = F.Id("z");
        var v = F.Id("v");
        var w = F.Id("w");
        var pi = F.Pi;
        var theta = Call("arccos", Call("cosine", b, y, z, F.D(1), v, w));
        var premises = And(
            Lt(F.D(1), b), Le(b, F.D(2)),
            Le(F.D(1), y), Le(y, F.D(2)), Le(b, y),
            Le(F.D(1), z), Le(z, F.D(2)), Le(b, z),
            Le(F.D(1), v), Le(v, F.D(2)), Le(b, v),
            Le(F.D(1), w), Le(w, F.D(2)), Le(b, w));
        var conclusion = And(
            Lt(theta, new Formula.Fraction(Mul(F.D(2), pi), F.D(9))),
            Lt(Mul(F.D(8), theta), Mul(F.D(2), pi)),
            Lt(Mul(F.D(9), theta), Mul(F.D(2), pi)));
        return All([("b", F.Id("Real")), ("y", F.Id("Real")),
                ("z", F.Id("Real")), ("v", F.Id("Real")), ("w", F.Id("Real"))],
            new Formula.Logic(premises, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula All((string Name, Formula Type)[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
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
