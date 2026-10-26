using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class RemoveWorktreesCommandTests
{
    [Theory]
    [InlineData("event")]
    [InlineData("status")]
    [InlineData("extra")]
    public void NamedRemovalRejectsInconsistentReceiptEnvelope(string malformed)
    {
        var rows = new List<object> { new { path = "/fixture/linked", outcome = "removed" } };
        if (malformed == "extra") rows.Add(new { path = "/fixture/unrequested", outcome = "removed" });
        var payload = JsonSerializer.Serialize(new { @event = malformed == "event" ? "unexpected" : "worktree_removal",
            status = malformed == "status" ? "failed" : "succeeded", items = rows });
        var runner = new ScriptedWorktreeProcessRunner(new InventoryRunner(), (file, _, _) => file == "python3"
            ? new ProcessOutput(0, Encoding.UTF8.GetBytes(payload), []) : null);
        AssertResult(RemoveWorktreesCommand.Run("/fixture/main", ["--names", "linked"], runner), 74, 0, 1, 0);
    }

    [Theory]
    [InlineData(68, "not a canonical refusal")]
    [InlineData(73, "")]
    [InlineData(73, "WORKTREE_RETAINED reason\nextra")]
    public void NamedRemovalRejectsMalformedEmptyRefusalEnvelope(int exit, string error)
    {
        var runner = new ScriptedWorktreeProcessRunner(new InventoryRunner(), (file, _, _) => file == "python3"
            ? new ProcessOutput(exit, [], Encoding.UTF8.GetBytes(error)) : null);
        var result = RemoveWorktreesCommand.Run("/fixture/main", ["--names", "linked"], runner);
        AssertResult(result, 74, 0, 1, 0);
    }

    [Fact]
    public void NamedRemovalAbnormalExitCannotBecomeSuccessfulFromCompletedReceipt()
    {
        var inventory = new InventoryRunner();
        var payload = JsonSerializer.Serialize(new { items = new[] { new { path = "/fixture/linked", outcome = "removed" } } });
        var runner = new ScriptedWorktreeProcessRunner(inventory, (file, _, _) => file == "python3"
            ? new ProcessOutput(17, Encoding.UTF8.GetBytes(payload), Encoding.UTF8.GetBytes("Traceback:\nOSError: named boundary cause\n")) : null);
        var result = RemoveWorktreesCommand.Run("/fixture/main", ["--names", "linked"], runner);
        AssertResult(result, 74, 0, 1, 0);
        Assert.Contains("OSError: named boundary cause", result.Output);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NamedRemovalKeepsScopedQualificationRefusalAndFailureDistinct(bool refused)
    {
        using var fixture = new RemovalFixture();
        var target = fixture.Add("qualification");
        var production = new ProductionWorktreeProcessRunner();
        var runner = new ScriptedWorktreeProcessRunner(production, (file, args, directory) =>
        {
            if (file != "python3" || !args.Contains("remove")) return null;
            var modified = args.ToArray();
            modified[2] = modified[2].Replace("sys.exit(sys.modules['worktree_protocol'].main())", $"""
                p = sys.modules['worktree_protocol']
                preservation = sys.modules['worktree_preservation']
                original = preservation.qualify
                calls = 0
                def inject(*args, **kwargs):
                    global calls
                    calls += 1
                    if calls == 2:
                        raise p.{(refused ? "Refused" : "GitFailure")}('scoped qualification cause')
                    return original(*args, **kwargs)
                preservation.qualify = inject
                sys.exit(p.main())
                """, StringComparison.Ordinal);
            return production.Run(file, modified, directory, TimeSpan.FromSeconds(60));
        });
        var result = WorktreeCommand.Run(fixture.Main, ["remove", "--names", "qualification"], runner);
        AssertResult(result, refused ? 73 : 74, 0, refused ? 0 : 1, refused ? 1 : 0);
        using var row = JsonDocument.Parse(result.Output.Split('\n')[0]);
        Assert.Contains("scoped qualification cause", row.RootElement.GetProperty("error").GetString());
        Assert.True(Directory.Exists(target));
    }
}
