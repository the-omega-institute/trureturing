namespace StrataLint.Scribe.Tests;

public sealed class FrozenLedgerParserSourceTests
{
    [Fact]
    public void CurrentLedgerParsersDoNotSynthesizeRetiredProjectionAliases()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound);
        var primitives = repository.ReadAllText(RepositoryRelativePath.Create(
            "tools/StrataLint.Engine/Ledger/Validation/FrozenLedgerValidationPrimitives.cs"));
        var history = repository.ReadAllText(RepositoryRelativePath.Create(
            "tools/StrataLint.Engine/Ledger/Validation/FrozenLedgerHistoryValidation.cs"));
        var candidate = repository.ReadAllText(RepositoryRelativePath.Create(
            "tools/StrataLint.Engine/Ledger/Validation/FrozenLedgerCandidateValidation.cs"));

        AssertRetiredProjectionAliasesAbsent(primitives);
        AssertRetiredProjectionAliasesAbsent(history);
        AssertRetiredProjectionAliasesAbsent(candidate);
    }

    private static void AssertRetiredProjectionAliasesAbsent(string source)
    {
        Assert.DoesNotContain("var caseClass = currentShape ?", source, StringComparison.Ordinal);
        Assert.DoesNotContain("var evaluation = currentShape ?", source, StringComparison.Ordinal);
        Assert.DoesNotContain("var expectedVerdict = currentShape", source, StringComparison.Ordinal);
        Assert.DoesNotContain("var inputFingerprint = currentShape ?", source, StringComparison.Ordinal);
        Assert.DoesNotContain("var semanticReceipt = currentShape ?", source, StringComparison.Ordinal);
        Assert.DoesNotContain("var truthState = currentShape ?", source, StringComparison.Ordinal);
    }
}
