using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class ParetoEqOnVectorEqualityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "ParetoEqOnVectorEquality.pareto_eq_on_iff_vector_eq";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under coordinate partial orders, the symmetric Pareto kernel is equality of gain vectors.",
        H("Symmetric Pareto Kernel and Vector Equality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pareto-eq-on-iff-vector-eq"),
                DeclarationHandle.Create(Declaration),
                H("The symmetric kernel is exactly gain-vector equality"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each benefit coordinate is compared in its given direction, "
                            + "while lifecycle cost and risk use the reversed burden "
                            + "direction inherited from weak Pareto dominance.")),
                    Paragraph(Text(
                        "Antisymmetry in all five partial orders turns the two independent "
                            + "dominance directions into equality of every coordinate; "
                            + "the converse is coordinate reflexivity."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Kernel(Formula value, Formula carrier, Formula left, Formula right) =>
        Call("ParetoEqOn", value, carrier, left, right);

    private static Formula Vector(Formula value, Formula action) =>
        Apply(value, Seq(action, Dot, D(1)));

    private static Formula TheoremFormula()
    {
        Formula action = F.Id("Action");
        Formula information = F.Id("Information");
        Formula residual = F.Id("Residual");
        Formula transfer = F.Id("Transfer");
        Formula cost = F.Id("Cost");
        Formula risk = F.Id("Risk");
        Formula value = F.Id("value");
        Formula finiteCarrier = F.Id("F");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula carrier = Call("ParetoCarrier", finiteCarrier);
        Formula gainVector = Call(
            "GainVector", information, residual, transfer, cost, risk);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, action, Comma, Sp, information, Comma, Sp,
            residual, Comma, Sp, transfer, Comma, Sp, cost, Comma, Sp, risk,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", action), CloseBracket, Comma, Sp,
            Call("PartialOrder", information), Comma, Sp,
            Call("PartialOrder", residual), Comma, Sp,
            Call("PartialOrder", transfer), Comma, RowBreak, Grp(),
            Call("PartialOrder", cost), Comma, Sp,
            Call("PartialOrder", risk), Comma, RowBreak, Grp(),
            value, Colon, Sp, action, Sp, To, Sp, gainVector, Comma, Sp,
            finiteCarrier, Colon, Sp, Call("Finset", action), Comma, RowBreak, Grp(),
            x, Comma, Sp, y, Colon, Sp, carrier, Comma, RowBreak, Grp(),
            Kernel(value, finiteCarrier, x, y), Sp, Iff, Sp,
            Vector(value, F.Id("x")), Sp, Eq, Sp, Vector(value, F.Id("y")), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
