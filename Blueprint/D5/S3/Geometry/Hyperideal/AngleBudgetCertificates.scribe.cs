using System;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class AngleBudgetCertificatesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/AngleBudgetCertificates.exact_angle_budget_certificates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact strict angle budgets for the CFMP Section 25.3 certificate.",
        H("The five Section 25.3 angle budgets"),
        Blocks(
            Paragraph(Text("Define betaTwo=arccos(70/99), "
                + "betaThree=arccos(49sqrt(6)/198), and "
                + "thetaZero=arccos(31/33), thetaOne=arccos(25/sqrt(726)), "
                + "thetaTwo=arccos(81/88).")),
            Describe.Lean(
                DescribeId.Create("exact-angle-budget-certificates"),
                DeclarationHandle.Create(Declaration),
                H("All five strict budgets"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each arccosine is bounded below by a rational "
                        + "angle using a quarter-angle sine remainder estimate. "
                        + "The proof then combines the five rational lower bounds "
                        + "with the exact upper bound pi<3.1416.")),
                    Paragraph(Text("The result is a numerical angle certificate for "
                        + "the prescribed CFMP local budgets. It does not construct "
                        + "edge lengths, prove a global cone metric, or establish "
                        + "the geometric realization bridge in later sections."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var pi = F.Pi;
        var betaTwo = Call("betaTwo");
        var betaThree = Call("betaThree");
        var thetaZero = Call("thetaZero");
        var thetaOne = Call("thetaOne");
        var thetaTwo = Call("thetaTwo");
        return And(
            Gt(Mul(F.D(8), betaTwo), Mul(F.D(2), pi)),
            Gt(AndTerm(Mul(F.D(6), betaThree), betaTwo), Mul(F.D(2), pi)),
            Gt(Mul(F.D(1, 8), thetaZero), Mul(F.D(2), pi)),
            Gt(AndTerm(Mul(F.D(1, 1), thetaOne), Mul(F.D(6), thetaZero)), Mul(F.D(2), pi)),
            Gt(AndTerm(Mul(F.D(9), thetaTwo), Mul(F.D(7), thetaOne)), Mul(F.D(2), pi)));
    }

    private static Formula And(params Formula[] parts)
    {
        if (parts.Length == 0) throw new ArgumentException("Empty conjunction");
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Gt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);
    private static Formula AndTerm(Formula left, Formula right) =>
        F.Seq(left, F.Plus, F.Sp, right);
    private static Formula Mul(Formula left, Formula right) =>
        F.Seq(left, F.Cdot, F.Sp, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
