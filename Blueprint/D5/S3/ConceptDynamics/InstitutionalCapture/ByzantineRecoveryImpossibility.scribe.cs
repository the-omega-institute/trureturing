using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class ByzantineRecoveryImpossibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula reporters = F.Id("n");
        Formula bound = F.Id("f");
        Formula truth = F.Id("truth");
        Formula reports = F.Id("reports");
        Formula recovery = F.Id("recovery");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reportVector = Seq(Call("Fin", reporters), Sp, To, Sp, F.Id("Bool"));
        Formula recoveryType = Seq(Open, reportVector, Close, Sp, To, Sp, F.Id("Bool"));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, reporters, Comma, Sp, bound, Sp, InMacro, Sp, naturals,
            Comma, Sp, reporters, Sp, Leq, Sp, D(2), Sp, Times, Sp, bound,
            RowBreak, Grp(),
            Rightarrow, Sp, Neg, Exists, Sp, recovery, Colon, Sp, recoveryType,
            Comma, RowBreak, Grp(),
            Forall, Sp, truth, Colon, Sp, F.Id("Bool"), Comma, Sp,
            reports, Colon, Sp, reportVector, Comma, RowBreak, Grp(),
            Call("byzantineCount", reports, truth), Sp, Leq, Sp, bound,
            Rightarrow, Sp, recovery, Open, reports, Close, Sp, Eq, Sp, truth, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "When no strict honest majority is guaranteed, report vectors cannot deterministically identify a Boolean truth under every allowed attack.",
            H("Worst-Case Byzantine Recovery Impossibility"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("deterministic-recovery-impossible"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/InstitutionalCapture/"
                            + "ByzantineRecoveryImpossibility."
                            + "deterministic_recovery_impossible"),
                    H("No deterministic recovery at or below half"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The report population is indexed by Fin n. The imported "
                                + "byzantineCount primitive counts reports that disagree with "
                                + "the common honest Boolean truth.")),
                        Paragraph(Text(
                            "Under n at most two f, the proof constructs one report vector "
                                + "within the allowed f disagreements of both truth values. A "
                                + "deterministic rule would have to return false and true on "
                                + "that same vector."))),
                    DescribeRole.Theorem))));
    }
}
