using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class TargetLaunderingCriterionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target laundering combines post-arrival protected-coordinate change, "
            + "same-round regrading, and attribution to the original commitment.",
        H("Target Laundering Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-laundering-criterion"),
                DeclarationHandle.Create(DeclarationPrefix + "target_laundering_criterion"),
                H("The boxed temporal definition regroups into three clauses"),
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
                            + "revised commitment and old evidence. Its timestamp remains data, "
                            + "not an extra premise of the boxed criterion.")),
                    Paragraph(Text(
                        "DECT 50.4 defines this clause by a strict comparison between the "
                            + "Time-valued first arrival and the revised freeze time. The later "
                            + "Lean sketch instead uses visibility at the freeze EventId.")),
                    Paragraph(Text(
                        "Those source formulations are not equivalent under the stated data: "
                            + "a record first seen exactly at the freeze event is visible there "
                            + "but does not arrive strictly before it. The Lean module retains "
                            + "the sketch separately; an exact bridge reconciles only the two "
                            + "arrival tests, while the sketch-only timestamp stays explicit."))),
                DescribeRole.Theorem))));

    private static Formula CriterionFormula()
    {
        Formula arrival = F.Id("arrival");
        Formula evaluate = F.Id("evaluate");
        Formula oldK = F.Id("oldK");
        Formula newK = F.Id("newK");
        Formula evidence = F.Id("Z");
        Formula report = F.Id("report");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, arrival, Comma, Sp, evaluate, Comma, Sp, oldK, Comma, Sp,
            newK, Comma, Sp, evidence, Comma, Sp, report, Comma, RowBreak, Grp(),
            Call("TargetLaundering", arrival, evaluate, oldK, newK, evidence, report),
            Sp, Iff, RowBreak, Grp(),
            Call("PostArrivalProtectedChange", arrival, oldK, newK, evidence),
            Sp, Land, RowBreak, Grp(),
            Call("RegradesOldRound", evaluate, oldK, newK, evidence, report),
            Sp, Land, RowBreak, Grp(),
            Call("AttributesToOriginalCommitment", evaluate, oldK, newK, evidence, report),
            Dot,
            End, Grp(F.Id("gathered"))));
    }
}
