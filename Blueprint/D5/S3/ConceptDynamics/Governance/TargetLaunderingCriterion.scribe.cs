using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class TargetLaunderingCriterionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target laundering combines post-arrival protected-coordinate change, an actual "
            + "re-evaluation, and attribution to the original commitment.",
        H("Target Laundering Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-laundering-criterion"),
                DeclarationHandle.Create(DeclarationPrefix + "target_laundering_criterion"),
                H("Target laundering has three necessary and sufficient clauses"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The protected projection retains target chain, domain, tolerance, "
                            + "conditions, comparator, baseline, and weight specification. "
                            + "A common access filtration records that the evidence arrived "
                            + "before the revised commitment event.")),
                    Paragraph(Text(
                        "The regrade report carries a verdict together with an equality to the "
                            + "actual evaluation of the revised commitment on the old evidence. "
                            + "The attribution clause therefore cannot be discharged by an "
                            + "arbitrary truth label.")),
                    Paragraph(Text(
                        "A finite positive control changes a protected condition while retaining "
                            + "the same verdict, so unequal scores are not required. Separate "
                            + "false-side controls make each of the three clauses fail in isolation."))),
                DescribeRole.Theorem))));

    private static Formula CriterionFormula()
    {
        Formula evaluate = F.Id("evaluate");
        Formula filtration = F.Id("filtration");
        Formula original = F.Id("original");
        Formula revised = F.Id("revised");
        Formula evidence = F.Id("evidence");
        Formula report = F.Id("report");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, evaluate, Comma, Sp, filtration, Comma, Sp, original, Comma, Sp,
            revised, Comma, Sp, evidence, Comma, RowBreak, Grp(),
            Forall, Sp, report, Colon, Sp, Call("RegradeReport", evaluate), Comma, RowBreak,
            Grp(),
            Call("TargetLaundering", evaluate, filtration, original, revised, evidence, report),
            Sp, Iff, RowBreak, Grp(),
            Call("PostArrivalProtectedChange", filtration, original, revised, evidence),
            Sp, Land, RowBreak, Grp(),
            Call("RegradesOldRound", original, revised, evidence, Call("Time", revised), report),
            Sp, Land, RowBreak, Grp(),
            Call("AttributesToOriginalCommitment", evaluate, original, revised, evidence, report),
            Dot,
            End, Grp(F.Id("gathered"))));
    }
}
