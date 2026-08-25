using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class TargetLaunderingCriterionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target laundering combines freeze visibility, protected-coordinate change, "
            + "same-round regrading, and attribution to the original commitment.",
        H("Target Laundering Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-laundering-criterion"),
                DeclarationHandle.Create(DeclarationPrefix + "target_laundering_criterion"),
                H("The canonical definition regroups into three clauses"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The old and revised commitments share one round index. Event identifiers "
                            + "and times remain independent types, and every protected coordinate "
                            + "is projected directly from the revised commitment.")),
                    Paragraph(Text(
                        "The regrade report is indexed by the actual evaluator. Its proof field "
                            + "certifies the reported verdict as the evaluator's value on the "
                            + "revised commitment and old evidence.")),
                    Paragraph(Text(
                        "A separate temporal predicate compares a Time-valued arrival with the "
                            + "revised freeze time. The source supplies no bridge equating that "
                            + "comparison with freeze-event visibility."))),
                DescribeRole.Theorem))));

    private static Formula CriterionFormula()
    {
        Formula evaluate = F.Id("evaluate");
        Formula oldK = F.Id("oldK");
        Formula newK = F.Id("newK");
        Formula evidence = F.Id("Z");
        Formula report = F.Id("report");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, evaluate, Comma, Sp, oldK, Comma, Sp, newK, Comma, Sp,
            evidence, Comma, Sp, report, Comma, RowBreak, Grp(),
            Call("TargetLaundering", evaluate, oldK, newK, evidence, report),
            Sp, Iff, RowBreak, Grp(),
            Call("FreezeVisibleProtectedChange", oldK, newK, evidence),
            Sp, Land, RowBreak, Grp(),
            Call("RegradesOldRound", evaluate, oldK, newK, evidence, report),
            Sp, Land, RowBreak, Grp(),
            Call("AttributesToOriginalCommitment", evaluate, oldK, newK, evidence, report),
            Dot,
            End, Grp(F.Id("gathered"))));
    }
}
