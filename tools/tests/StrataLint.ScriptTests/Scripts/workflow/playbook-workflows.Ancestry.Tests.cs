using System.Text;
using System.Text.Json;

namespace StrataLint.ScriptTests;

public sealed partial class PlaybookWorkflowsTests
{
    [Fact]
    public void DeliverCheckRejectsAddedFreezeWhoseBaseWasRewrittenOutOfHeadHistory()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var deliveryBase = fixture.HeadRevision();
        fixture.ChangeFormalization();
        var frozenBase = fixture.CommitAll("snapshot before freeze");
        var eventPath = fixture.WriteAcceptedFreezeForBase(frozenBase);
        fixture.CommitAll("record freeze");
        fixture.RewriteHeadWithParent(deliveryBase);

        var result = fixture.Run("deliver-check", baseRevision: deliveryBase);

        Assert.Equal(1, result.ExitCode);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("PLAYBOOK_INVALID", error, StringComparison.Ordinal);
        Assert.Contains(eventPath, error, StringComparison.Ordinal);
        Assert.Contains("is not an ancestor of current HEAD", error, StringComparison.Ordinal);
        Assert.Contains("re-freeze from a pushed base", error, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-append", fixture.Calls());
        Assert.DoesNotContain("make:preflight", fixture.Calls());
    }

    [Fact]
    public void DeliverCheckAcceptsAddedFreezeWhoseBaseRemainsInHeadHistory()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var deliveryBase = fixture.HeadRevision();
        fixture.ChangeFormalization();
        var frozenBase = fixture.CommitAll("snapshot before freeze");
        fixture.WriteAcceptedFreezeForBase(frozenBase);
        fixture.CommitAll("record freeze");

        var result = fixture.Run("deliver-check", baseRevision: deliveryBase);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("make:preflight BASE=" + deliveryBase, fixture.Calls());
    }

    internal sealed partial class TransactionFixture
    {
        internal string HeadRevision() => Git("rev-parse", "HEAD").Trim();

        internal string CommitAll(string message)
        {
            Git("add", "-A");
            Git("commit", "-qm", message);
            return HeadRevision();
        }

        internal string WriteAcceptedFreezeForBase(string baseCommit)
        {
            var identity = new string('4', 64);
            var relativePath = $"{LedgerPath}/{identity}.json";
            var baseTree = Git("rev-parse", $"{baseCommit}^{{tree}}").Trim();
            var descriptorBlob = Git("rev-parse", $"{baseCommit}:{LeanPath}").Trim();
            WriteFile(relativePath, JsonSerializer.Serialize(new
            {
                event_type = "Freeze",
                payload = new
                {
                    input = new
                    {
                        base_commit_oid = "git-sha1:" + baseCommit,
                        base_tree_oid = "git-sha1:" + baseTree,
                        descriptor_blob_oid = "git-sha1:" + descriptorBlob,
                        descriptor_selector = LeanPath,
                        supporting_blob_oids = Array.Empty<string>(),
                    },
                },
            }) + "\n");
            return relativePath;
        }

        internal void RewriteHeadWithParent(string parent)
        {
            var tree = Git("rev-parse", "HEAD^{tree}").Trim();
            var rewritten = Git("commit-tree", tree, "-p", parent, "-m", "rewritten delivery").Trim();
            Git("reset", "--hard", rewritten);
        }
    }
}
