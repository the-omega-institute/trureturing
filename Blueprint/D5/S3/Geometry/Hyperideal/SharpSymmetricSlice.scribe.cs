using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SharpSymmetricSliceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/SharpSymmetricSlice.sharp_symmetric_slice";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact identities on the symmetric sharp slice.",
        H("The symmetric slice is algebraically sharp"),
        Blocks(
            Paragraph(Text("On the slice o=r, A=B=h and zeta=0, write t=xi^2. "
                + "The asymmetric remainder becomes 2(r^2-1)t+t^2. "
                + "The square-root radius simplifies to (r+1)(1+2h-r). "
                + "The result is an exact algebraic identity for every r>1 and h>1; "
                + "it does not assert a global CFMP realization.")),
            Describe.Lean(
                DescribeId.Create("sharp-symmetric-slice-identities"),
                DeclarationHandle.Create(Declaration),
                H("Exact remainder and radius"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first conjunct evaluates the full four-term "
                        + "asymmetry polynomial after the symmetric substitutions. "
                        + "The second conjunct evaluates the positive square root "
                        + "using r>1 and h>1.")),
                    Paragraph(Text("This is a local six-coordinate identity. It supplies "
                        + "the sharp slice calculation used in the surrounding stability "
                        + "argument, without claiming that the averaged slice is a global "
                        + "zero-curvature solution."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = F.Id("r");
        var h = F.Id("h");
        var xi = F.Id("xi");
        var xiSq = Pow(xi, F.D(2));
        var remainder = Call("Xi", r, r, h, h, xi, F.D(0));
        var remainderValue = Add(Mul(Mul(F.D(2), Sub(Pow(r, F.D(2)), F.D(1))), xiSq),
            Pow(xiSq, F.D(2)));
        var radius = Sub(Call("sqrt", Add(Pow(Sub(Pow(r, F.D(2)), F.D(1)), F.D(2)),
            Mul(Call("L", r, r, h, h), Call("M", r, r, h, h)))),
            Sub(Pow(r, F.D(2)), F.D(1)));
        var radiusValue = Mul(Add(r, F.D(1)), Sub(Add(F.D(1), Mul(F.D(2), h)), r));
        var conclusion = And(Equal(remainder, remainderValue), Equal(radius, radiusValue));
        return All([("r", F.Id("Real")), ("h", F.Id("Real")), ("xi", F.Id("Real"))],
            new Formula.Logic(
                And(Lt(F.D(1), r), Lt(F.D(1), h)),
                FormulaLogicOperator.Implies,
                conclusion));
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
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        Group(F.Seq(left, F.Plus, right));
    private static Formula Sub(Formula left, Formula right) =>
        Group(F.Seq(left, F.Minus, right));
    private static Formula Mul(Formula left, Formula right) =>
        Group(F.Seq(left, F.Cdot, F.Sp, right));
    private static Formula Pow(Formula left, Formula right) =>
        Group(F.Seq(left, F.Caret, right));
    private static Formula Group(Formula value) =>
        F.Seq(F.Open, value, F.Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
