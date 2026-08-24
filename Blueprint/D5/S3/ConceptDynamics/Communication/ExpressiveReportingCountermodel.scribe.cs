using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class ExpressiveReportingCountermodelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A report carrier can encode every type while incentives still select a nontruthful report.",
        H("Expressive Reporting Countermodel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("expressive-report-space-does-not-force-truthful-revelation"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Communication/ExpressiveReportingCountermodel."
                        + "expressive_report_space_does_not_force_truthful_revelation"),
                H("Expressive report capacity does not force truthful revelation"),
                StatementSource.FromAuthor(CountermodelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The type carrier and report carrier are both Bool, and the profile's "
                            + "truthful direct report is the identity. The report interface can "
                            + "therefore encode either true type without loss.")),
                    Paragraph(Text(
                        "The mechanism uses the reported Boolean as its outcome. Utility is one "
                            + "at outcome false and zero at outcome true for both types, so both "
                            + "types strictly prefer the result induced by report false.")),
                    Paragraph(Text(
                        "The sent strategy is constantly false and is utility-maximizing against "
                            + "every alternative report. In particular, true type true reports "
                            + "false, and the sent strategy differs from truthful reporting.")),
                    Paragraph(Text(
                        "This explicit strategic countermodel separates expressive capacity from "
                            + "truthful revelation; the missing ingredient is an incentive "
                            + "condition, not another report symbol."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula CountermodelFormula()
    {
        Formula profile = F.Id("p");
        Formula mechanism = F.Id("g");
        Formula utility = F.Id("u");
        Formula trueType = F.Id("theta");
        Formula report = F.Id("r");
        Formula boolType = Seq(Operatorname, Grp(F.Id("Bool")));
        Formula realType = Seq(Mathbb, Grp(F.Id("R")));
        Formula profileType = Call("ReportProfile", boolType, boolType, boolType);
        Formula sent = Seq(profile, Dot, F.Id("sentReport"));
        Formula truthful = Seq(profile, Dot, F.Id("trueReport"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp, Typed(profile, profileType), Comma, Sp,
            Typed(mechanism, new Formula.TypeArrow(boolType, boolType)), Comma,
            RowBreak, Grp(),
            Typed(utility,
                new Formula.TypeArrow(boolType,
                    new Formula.TypeArrow(boolType, realType))), Comma,
            RowBreak, Grp(),
            truthful, Sp, Eq, Sp, F.Id("id"), Sp, Land, RowBreak, Grp(),
            Apply(sent, F.Id("true")), Sp, Eq, Sp, F.Id("false"), Sp, Land,
            RowBreak, Grp(),
            sent, Sp, Neq, Sp, truthful, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, Typed(trueType, boolType), Comma, Sp,
            Apply(utility, trueType, Apply(mechanism, F.Id("false"))), Sp, Gt, Sp,
            Apply(utility, trueType, Apply(mechanism, F.Id("true"))), Close,
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(Seq(trueType, Comma, Sp, report), boolType), Comma, Sp,
            Apply(utility, trueType, Apply(mechanism, Apply(sent, trueType))),
            Sp, Geq, Sp, Apply(utility, trueType, Apply(mechanism, report)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
