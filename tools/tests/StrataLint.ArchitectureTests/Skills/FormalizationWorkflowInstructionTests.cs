namespace StrataLint.ArchitectureTests;

public sealed class FormalizationWorkflowInstructionTests
{
    [Fact]
    public void WorktreeDisciplineDoesNotRequireCommittedBlobBeforeDeposit()
    {
        var instructions = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "CLAUDE.md"));

        Assert.DoesNotContain("未提交 blob", instructions, StringComparison.Ordinal);
        Assert.Contains("repository.ReadCurrent()", instructions, StringComparison.Ordinal);
        Assert.Contains("只改工作树、不自动提交", instructions, StringComparison.Ordinal);
    }

    [Fact]
    public void BatchDepositLaneDocumentsFourArtifacts()
    {
        var script = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools",
            "scripts",
            "agent",
            "batch_pr.sh"));

        Assert.Contains(
            "每条四件(Lean / scribe.cs / md / 冻结条目)",
            script,
            StringComparison.Ordinal);
    }

    [Fact]
    public void FormalAnswerSkillDoesNotImportRetiredFormalizationReceiptLedger()
    {
        var skill = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-formal-answer",
            "SKILL.md"));

        Assert.DoesNotContain("receipt-ledger", skill, StringComparison.OrdinalIgnoreCase);
        Assert.Contains(
            "Do not import freezing, deposit, coverage, or truth-DAG publication machinery.",
            skill,
            StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryIngestSkillTreatsLedgerAsEvidenceRatherThanFormalizationReceipt()
    {
        var skill = File.ReadAllText(Path.Combine(
            RepositoryLayout.FindRoot(),
            "skills",
            "codex-theory-ingest",
            "SKILL.md"));

        Assert.DoesNotContain("supplies that receipt", skill, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("supplies that evidence", skill, StringComparison.Ordinal);
        Assert.DoesNotContain(
            "coverage, and receipts are owned",
            skill,
            StringComparison.OrdinalIgnoreCase);
        Assert.Contains(
            "freezing, and coverage edges are owned",
            skill,
            StringComparison.Ordinal);
    }
}
