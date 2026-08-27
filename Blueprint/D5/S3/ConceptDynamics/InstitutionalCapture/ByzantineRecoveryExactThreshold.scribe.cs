using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class ByzantineRecoveryExactThresholdDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InstitutionalCapture/ByzantineRecoveryExactThreshold."
            + "deterministic_recovery_exact_threshold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal deterministic Boolean recovery holds exactly above twice the fault bound.",
        H("Exact Threshold for Byzantine Recovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("deterministic-recovery-exact-threshold"),
            DeclarationHandle.Create(Declaration),
            H("The strict honest-majority threshold is exact"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Reports form a Boolean vector indexed by Fin n. The canonical "
                        + "byzantineCount counts entries that disagree with the common truth, "
                        + "and the recovery rule receives only that report vector.")),
                Paragraph(Text(
                    "At or below twice the fault bound, the frozen impossibility theorem "
                        + "constructs one vector compatible with both truths. Above the bound, "
                        + "the canonical strict-majority rule returns the truth for every "
                        + "allowed report vector, proving the converse at the same threshold."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula truth = F.Id("truth");
        Formula reports = F.Id("reports");
        Formula recovery = F.Id("recovery");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula boolType = F.Id("Bool");
        Formula reportVector = Arrow(Call("Fin", n), boolType);
        Formula recoveryType = Arrow(Seq(Open, reportVector, Close), boolType);
        Formula recoversEveryAllowedVector = Seq(
            Exists, Sp, recovery, Colon, Sp, recoveryType, Comma, Sp,
            Forall, Sp, truth, Colon, Sp, boolType, Comma, Sp,
            reports, Colon, Sp, reportVector, Comma, Sp,
            Call("byzantineCount", reports, truth), Sp, Leq, Sp, f,
            Sp, Rightarrow, Sp,
            recovery, Open, reports, Close, Sp, Eq, Sp, truth);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Comma, Sp, f, Sp, InMacro, Sp, naturals, Comma),
            Seq(Open, recoversEveryAllowedVector, Close, Sp, Iff, Sp,
                n, Sp, Gt, Sp, D(2), Sp, Times, Sp, f, Dot),
        ]));
    }
}
