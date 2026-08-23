using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class VoluntarinessActionFactorizationObstructionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal actions with different voluntariness status obstruct action-only evaluation.",
        H("Voluntariness Action-Factorization Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("action-result-does-not-identify-voluntariness"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/NormativeStructure/"
                        + "VoluntarinessActionFactorizationObstruction."
                        + "action_result_does_not_identify_voluntariness"),
                H("An action result does not identify voluntariness"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The path carrier, action readout, and normative voluntariness evaluation "
                            + "are independent public source primitives on the canonical concept "
                            + "carrier. The freely chosen and coerced paths are also public.")),
                    Paragraph(Text(
                        "The hypotheses state that the two paths have one action result but "
                            + "different authorization status. The conclusion directly denies any "
                            + "function of the action result through which the full voluntariness "
                            + "evaluation factors.")),
                    Paragraph(Text(
                        "Repository search found the exact frozen family theorem for equal "
                            + "endpoints with different normative evaluations. The Lean proof "
                            + "packages the two named paths as its witness and applies that theorem "
                            + "directly, with no local reproof or duplicate provenance primitive.")),
                    Paragraph(Text(
                        "A constant Unit-valued action and identity Boolean evaluation compile as "
                            + "a concrete inhabited model of the hypotheses."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula pathType = F.Id("Gamma");
        Formula actionType = F.Id("Action");
        Formula statusType = F.Id("AuthorizationStatus");
        Formula action = F.Id("A");
        Formula voluntariness = F.Id("V");
        Formula freelyChosen = F.Id("gamma");
        Formula coerced = F.Id("gammaPrime");
        Formula factor = F.Id("v");
        Formula sameAction = Seq(
            Apply(action, freelyChosen), Sp, Eq, Sp, Apply(action, coerced));
        Formula differentStatus = Seq(
            Apply(voluntariness, freelyChosen), Sp, Neq, Sp,
            Apply(voluntariness, coerced));
        Formula reduction = Seq(
            Exists, Sp, factor, Colon, Sp, Arrow(actionType, statusType), Comma, Sp,
            voluntariness, Sp, Eq, Sp, Call("compose", factor, action));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, pathType, Comma, Sp, actionType, Comma, Sp, statusType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            action, Colon, Sp, Arrow(pathType, actionType), Comma, Sp,
            voluntariness, Colon, Sp, Arrow(pathType, statusType), Comma,
            RowBreak, Grp(),
            freelyChosen, Comma, Sp, coerced, Colon, Sp, pathType, Comma,
            RowBreak, Grp(),
            sameAction, Sp, Land, Sp, differentStatus, Sp, Rightarrow,
            RowBreak, Grp(),
            Neg, Sp, Open, reduction, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
