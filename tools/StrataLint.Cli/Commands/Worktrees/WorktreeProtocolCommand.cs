using System.Text;
using System.Text.Json;
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
        using var program = new EmbeddedProgramFile(Program.Value
            + "sys.exit(sys.modules['worktree_protocol'].main())\n");
        var result = runner.Run("python3", new[] { "-I", "-B", program.FilePath,
            "--source", root }.Concat(arguments).ToArray(),
            root, timeout ?? BoundedProcessRunner.HangDetectionBudget);
        return new CommandResult(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput),
            Encoding.UTF8.GetString(result.StandardError), result.ExitCode);
    }

    internal static CommandResult RunLines(string root, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner, TimeSpan timeout, Action<string> consume)
    {
        using var program = new EmbeddedProgramFile(Program.Value
            + "sys.exit(sys.modules['worktree_protocol'].main())\n");
        var result = runner.RunStreaming("python3", new[] { "-I", "-B", program.FilePath,
            "--source", root }.Concat(arguments).ToArray(),
            root, timeout, async (stream, cancellation) =>
            {
                using var reader = new StreamReader(stream, Encoding.UTF8);
                var buffer = new char[4096];
                var line = new StringBuilder();
                while (true)
                {
                    var count = await reader.ReadAsync(buffer.AsMemory(), cancellation);
                    if (count == 0) break;
                    for (var index = 0; index < count; index++)
                    {
                        if (buffer[index] == '\n')
                        {
                            consume(line.ToString());
                            line.Clear();
                        }
                        else
                        {
                            if (line.Length >= 64 * 1024)
                                throw new InvalidOperationException("qualification row exceeded 65536 characters");
                            line.Append(buffer[index]);
                        }
                    }
                }
                if (line.Length != 0) throw new InvalidOperationException("incomplete qualification row:"
                    + CleanLanesCommand.BoundedDiagnostic(line.ToString()));
                return 0;
            });
        return new CommandResult(result.ExitCode == 0, string.Empty,
            Encoding.UTF8.GetString(result.StandardError), result.ExitCode);
    }

    internal static IReadOnlyDictionary<string, string> InitializationEnvironment(string root)
    {
        // Export ambient names and generated policy values only; ambient values stay local.
        using var program = new EmbeddedProgramFile(Program.Value
            + "import json\np = sys.modules['worktree_protocol']\n"
            + "print(json.dumps(dict(Inherited=list(p.inherited_environment()), Scoped=p.scoped_process_environment())))\n");
        var result = new ProductionWorktreeProcessRunner().Run("python3", ["-I", "-B", program.FilePath],
            root, BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode != 0)
            throw new InvalidOperationException(Encoding.UTF8.GetString(result.StandardError));
        var policy = JsonSerializer.Deserialize<InitializationPolicy>(result.StandardOutput)
            ?? throw new InvalidOperationException("worktree environment policy is absent");
        var environment = policy.Inherited.Where(name => Environment.GetEnvironmentVariable(name) is not null)
            .ToDictionary(name => name, name => Environment.GetEnvironmentVariable(name)!);
        foreach (var (name, value) in policy.Scoped) environment[name] = value;
        return environment;
    }

    private sealed record InitializationPolicy(string[] Inherited, Dictionary<string, string> Scoped);

    // A private, per-call file carries the build's embedded bytes without growing
    // argv or environment strings. Python stays isolated from checkout imports.
    private sealed class EmbeddedProgramFile : IDisposable
    {
        private readonly DirectoryInfo directory = Directory.CreateTempSubdirectory("stratalint-worktree-");
        internal string FilePath { get; }

        internal EmbeddedProgramFile(string program)
        {
            FilePath = Path.Combine(directory.FullName, "adapter.py");
            try
            {
                var options = new FileStreamOptions { Mode = FileMode.CreateNew, Access = FileAccess.Write };
                if (!OperatingSystem.IsWindows())
                    options.UnixCreateMode = UnixFileMode.UserRead | UnixFileMode.UserWrite;
                using var stream = new FileStream(FilePath, options);
                stream.Write(Encoding.UTF8.GetBytes(program));
            }
            catch
            {
                Dispose();
                throw;
            }
        }

        public void Dispose()
        {
            File.Delete(FilePath);
            directory.Delete();
        }
    }

    private static string LoadProgram()
    {
        var assembly = typeof(WorktreeProtocolCommand).Assembly;
        var program = new StringBuilder("import base64, sys, types\n");
        // Dependency order: both operations import protocol; preservation's
        // commit_snapshot import consumes publication. These modules use only
        // host Python standard-library modules and native Git beyond this set.
        foreach (var name in new[] { "worktree_protocol", "worktree_publication", "worktree_preservation", "worktree_pool" })
        {
            using var stream = assembly.GetManifestResourceStream($"WorktreeProtocol.{name}.py")
                ?? throw new InvalidOperationException($"worktree adapter module is unavailable: {name}");
            using var bytes = new MemoryStream();
            stream.CopyTo(bytes);
            program.Append($"m = types.ModuleType('{name}')\nsys.modules['{name}'] = m\n");
            program.Append($"exec(compile(base64.b64decode('{Convert.ToBase64String(bytes.ToArray())}'), '{name}.py', 'exec'), m.__dict__)\n");
        }
        return program.ToString();
    }
}
