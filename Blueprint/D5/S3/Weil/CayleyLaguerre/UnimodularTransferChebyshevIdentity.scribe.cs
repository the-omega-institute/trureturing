using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class UnimodularTransferChebyshevIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/CayleyLaguerre/UnimodularTransferChebyshevIdentity."
            + "unimodular_transfer_chebyshev_identities";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unimodular two-by-two transfer power traces realize first-kind Chebyshev values.",
        H("Unimodular Transfer Chebyshev Identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("unimodular-transfer-chebyshev-identities"),
            DeclarationHandle.Create(Declaration),
            H("Trace powers and Chebyshev slack"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The frozen two-by-two trace-power theorem reduces the matrix power "
                        + "trace to the power sum of the roots of its characteristic "
                        + "quadratic. Mathlib's Dickson identity then identifies that sum "
                        + "with the first-kind Chebyshev polynomial.")),
                Paragraph(Text(
                    "Substitution of the trace identity gives the displayed slack equality "
                        + "by polynomial arithmetic."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Observation/MatrixTracePowerSum")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Chebyshev(Formula degree, Formula value) =>
        new Formula.Apply(new Formula.Subscript(F.Id("T"), degree), [value]);

    private static Formula TheoremFormula()
    {
        Formula matrix = F.Id("M");
        Formula degree = F.Id("N");
        Formula x = F.Id("x");
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula specialLinear = Seq(
            F.Id("SL"), Underscore, Grp(D(2)), Open, complexes, Close);
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula quarter = new Formula.Fraction(D(1), D(4));
        Formula trace = Call("tr", matrix);
        Formula powerTrace = Call("tr", Power(matrix, degree));
        Formula value = Chebyshev(degree, x);
        Formula halfTrace = Seq(half, Sp, Times, Sp, trace);
        Formula halfPowerTrace = Seq(half, Sp, Times, Sp, powerTrace);
        Formula traceIdentity = new Formula.Relation(
            halfPowerTrace, FormulaRelationOperator.Equal, value);
        Formula slackIdentity = new Formula.Relation(
            Seq(D(1), Sp, Minus, Sp, Power(Grp(value), D(2))),
            FormulaRelationOperator.Equal,
            Seq(
                Minus, quarter, Sp, Times, Sp, Open,
                Power(powerTrace, D(2)), Sp, Minus, Sp, D(4), Close));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, matrix, Colon, Sp, specialLinear, Comma, Sp,
                degree, InMacro, Sp, naturals, Comma),
            Seq(
                Grp(), F.Id("let"), Sp, x, Colon, Sp, complexes, Sp, Eq, Sp,
                halfTrace, Semi),
            Seq(Grp(), traceIdentity, Sp, Land),
            Seq(Grp(), slackIdentity, Dot),
        ]));
    }
}
