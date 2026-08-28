using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class GainDifferenceCocycleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/GainDifferenceCocycle."
            + "gain_difference_self_zero_and_cocycle";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five heterogeneous additive gain coordinates telescope exactly.",
        H("Gain Difference Cocycle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gain-difference-self-zero-and-cocycle"),
                DeclarationHandle.Create(Declaration),
                H("Gain differences have zero self-value and a three-point cocycle"),
                StatementSource.FromAuthor(GainDifferenceCocycleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary action type, each action receives one vector with "
                            + "independently typed information, residual-capture, transfer, "
                            + "lifecycle-cost, and risk coordinates. Each coordinate is an "
                            + "additive group, and gainDifference subtracts absolute values "
                            + "coordinate by coordinate.")),
                    Paragraph(Text(
                        "Scalar self-subtraction proves the first clause. In the second clause, "
                            + "the intermediate absolute value cancels independently in all five "
                            + "coordinates by sub_add_sub_cancel, yielding the direct difference.")),
                    Paragraph(Text(
                        "This closes the first half of proof obligation 10 in "
                            + "definition-escape-completion-theory atom "
                            + "generic-residual-8f550f340a56075d2e0b7a070a3f78814a780adf06d7f6677736a277f7a39cb3. "
                            + "The separate no-source-weight implication is not asserted here."))),
                DescribeRole.Theorem))));

    private static Formula Difference(
        Formula value, Formula first, Formula second) =>
        Call("gainDifference", value, first, second);

    private static Formula GainDifferenceCocycleFormula()
    {
        Formula action = F.Id("Action");
        Formula information = F.Id("Information");
        Formula residual = F.Id("Residual");
        Formula transfer = F.Id("Transfer");
        Formula cost = F.Id("Cost");
        Formula risk = F.Id("Risk");
        Formula value = F.Id("value");
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula third = F.Id("c");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula gainVector = Call(
            "GainVector", information, residual, transfer, cost, risk);

        Formula AddGroup(Formula coordinate) =>
            Seq(OpenBracket, Call("AddGroup", coordinate), CloseBracket);

        Formula selfZero = Seq(
            Forall, Sp, first, Colon, Sp, action, Comma, Sp,
            Difference(value, first, first), Sp, Eq, Sp, D(0));
        Formula cocycle = Seq(
            Forall, Sp, first, Comma, Sp, second, Comma, Sp, third,
            Colon, Sp, action, Comma, Sp,
            Difference(value, first, third), Sp, Eq, Sp,
            Difference(value, first, second), Sp, Plus, Sp,
            Difference(value, second, third));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, action, Comma, Sp, information, Comma, Sp,
            residual, Comma, Sp, transfer, Comma, Sp, cost, Comma, Sp, risk,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            AddGroup(information), Comma, Sp,
            AddGroup(residual), Comma, Sp,
            AddGroup(transfer), Comma, Sp,
            AddGroup(cost), Comma, Sp,
            AddGroup(risk), Comma, RowBreak, Grp(),
            value, Colon, Sp, action, Sp, To, Sp, gainVector, Comma, RowBreak, Grp(),
            Open, selfZero, Close, Sp, Land, RowBreak, Grp(),
            Open, cocycle, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
