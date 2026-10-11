using System.Text;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static class WorktreeProtocolCommand
{
    // Program identity belongs to this CLI build, independently of the Git
    // repository/cwd used by an operation. Keep the complete adapter in memory
    // before any removal; neither a later call nor a Python import reopens a
    // disposable checkout to obtain executable code.
    private static readonly Lazy<string> Program = new(LoadProgram);

    internal static CommandResult Run(string root, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner, TimeSpan? timeout = null)
    {
        // Isolated Python imports host libraries without searching a repository
        // cwd or PYTHONPATH for another implementation of a support module.
        var result = runner.Run("python3", new[] { "-IB", "-c", Program.Value, "--source", root }.Concat(arguments).ToArray(),
            root, timeout ?? BoundedProcessRunner.HangDetectionBudget);
        return new CommandResult(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput),
            Encoding.UTF8.GetString(result.StandardError), result.ExitCode);
    }

    private static string LoadProgram()
    {
        var assembly = typeof(WorktreeProtocolCommand).Assembly;
        var program = new StringBuilder("import base64, sys, types\n");
        // Dependency order: both operations import protocol; preservation's
        // commit_snapshot import consumes publication. All three use only
        // host Python standard-library modules and native Git beyond this set.
        foreach (var name in new[] { "worktree_protocol", "worktree_publication", "worktree_preservation" })
        {
            using var stream = assembly.GetManifestResourceStream($"WorktreeProtocol.{name}.py")
                ?? throw new InvalidOperationException($"worktree adapter module is unavailable: {name}");
            using var bytes = new MemoryStream();
            stream.CopyTo(bytes);
            program.Append($"m = types.ModuleType('{name}')\nsys.modules['{name}'] = m\n");
            program.Append($"exec(compile(base64.b64decode('{Convert.ToBase64String(bytes.ToArray())}'), '{name}.py', 'exec'), m.__dict__)\n");
        }
        program.Append("sys.exit(sys.modules['worktree_protocol'].main())\n");
        return program.ToString();
    }
}
