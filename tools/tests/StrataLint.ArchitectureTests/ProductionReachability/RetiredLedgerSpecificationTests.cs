namespace StrataLint.ArchitectureTests;

public sealed class RetiredLedgerSpecificationTests
{
    [Fact]
    public void CurrentSpecificationMarksSupersedeProtocolRetired()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "docs/develop/spec/golden-ledger-repo-spec.md");
        var text = File.ReadAllText(path);

        Assert.Contains("**A14（retired）", text, StringComparison.Ordinal);
        Assert.DoesNotContain("现役第五事件 `Supersede`", text, StringComparison.Ordinal);
        Assert.DoesNotContain("支持命令为 `ledger-supersede", text, StringComparison.Ordinal);
        Assert.DoesNotContain("operation 枚举仅 `Genesis|Freeze|Reattest|Supersede|Revoke`", text, StringComparison.Ordinal);
        Assert.DoesNotContain("| current \\\\ incoming | Genesis | Freeze | Reattest | Supersede | Revoke |", text, StringComparison.Ordinal);
    }
}
