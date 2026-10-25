using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class RemoveWorktreesCommandTests
{
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
