using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record ConservativeRepositoryIdentity(string CommitOid, string TreeOid);

internal sealed record ConservativeHarnessProgram(string DllPath, string Root);

internal sealed record ConservativeHarnessInvocation(
    ConservativeHarnessProgram Program,
    MaterializedConservativeCorpus Corpus,
    string BaselineRoot,
    string CandidateRoot,
    ConservativeRepositoryIdentity BaselineIdentity,
    ConservativeRepositoryIdentity CandidateIdentity,
    string BaselineLeanReport,
    string CandidateLeanReport);

internal interface IConservativeExtensionEnvironment
{
    MaterializedConservativeCorpus Materialize(string baselineRoot);

    ConservativeRepositoryIdentity IdentifyRepository(string root);

    ConservativeHarnessProgram LoadHarness(string root);

    string FileRoot(string path);

    ConservativeHarnessExecution Execute(ConservativeHarnessInvocation invocation);
}

internal static class ConservativeExtensionCommand
{
    internal const string BaseTreeCaseId = "actual:baseline-tree";
    internal const string CandidateTreeCaseId = "actual:candidate-tree";

    internal static ExplicitCommandResult Run(IReadOnlyList<string> arguments) =>
        Run(arguments, new ProductionConservativeExtensionEnvironment());

    internal static ExplicitCommandResult Run(
        IReadOnlyList<string> arguments,
        IConservativeExtensionEnvironment environment)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(environment);
        try
        {
            var options = Parse(arguments);
            var corpus = environment.Materialize(options.BaselineRoot);
            if (corpus.CaseIds.IsDefaultOrEmpty
                || corpus.CaseIds.Contains(BaseTreeCaseId, StringComparer.Ordinal)
                || corpus.CaseIds.Contains(CandidateTreeCaseId, StringComparer.Ordinal))
            {
                throw new InvalidOperationException("base-owned golden corpus has an invalid case set");
            }

            var baselineIdentity = environment.IdentifyRepository(options.BaselineRoot);
            var candidateIdentity = environment.IdentifyRepository(options.CandidateRoot);
            var baselineProgram = environment.LoadHarness(options.BaselineRoot);
            var candidateProgram = environment.LoadHarness(options.CandidateRoot);
            var invocation = new ConservativeHarnessInvocation(
                baselineProgram,
                corpus,
                options.BaselineRoot,
                options.CandidateRoot,
                baselineIdentity,
                candidateIdentity,
                options.BaselineLeanReport,
                options.CandidateLeanReport);
            var baselineExecution = environment.Execute(invocation);
            var candidateExecution = environment.Execute(invocation with { Program = candidateProgram });
            var input = new ConservativeVerificationInput(
                baselineIdentity.CommitOid,
                baselineIdentity.TreeOid,
                candidateIdentity.CommitOid,
                candidateIdentity.TreeOid,
                baselineProgram.Root,
                candidateProgram.Root,
                environment.FileRoot(options.BaselineLeanReport),
                environment.FileRoot(options.CandidateLeanReport),
                corpus.Root,
                corpus.CaseIds.Add(BaseTreeCaseId),
                corpus.CaseIds.Length,
                BaseTreeCaseId,
                CandidateTreeCaseId,
                baselineExecution,
                candidateExecution);
            return ConservativeExtensionVerifier.Verify(input) switch
            {
                ConservativeExtensionOutcome.Accepted accepted => new ExplicitCommandResult(
                    0,
                    StrictUtf8(accepted.Certificate),
                    string.Empty),
                ConservativeExtensionOutcome.Violated violated => new ExplicitCommandResult(
                    1,
                    StrictUtf8(violated.Certificate),
                    string.Empty),
                ConservativeExtensionOutcome.InfrastructureFailure failure =>
                    Infrastructure(failure.Message),
                _ => throw new InvalidOperationException("unknown conservative extension outcome"),
            };
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return Infrastructure(exception.Message);
        }
    }

    private static ConservativeCommandOptions Parse(IReadOnlyList<string> arguments)
    {
        string? baselineRoot = null;
        string? candidateRoot = null;
        string? baselineLeanReport = null;
        string? candidateLeanReport = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count) throw Usage();
            var value = arguments[index + 1];
            switch (arguments[index])
            {
                case "--baseline-root" when baselineRoot is null:
                    baselineRoot = RequireDirectory(value, "baseline root");
                    break;
                case "--candidate-root" when candidateRoot is null:
                    candidateRoot = RequireDirectory(value, "candidate root");
                    break;
                case "--baseline-lean-report" when baselineLeanReport is null:
                    baselineLeanReport = RequireFile(value, "baseline Lean report");
                    break;
                case "--candidate-lean-report" when candidateLeanReport is null:
                    candidateLeanReport = RequireFile(value, "candidate Lean report");
                    break;
                default:
                    throw Usage();
            }
        }

        if (baselineRoot is null
            || candidateRoot is null
            || baselineLeanReport is null
            || candidateLeanReport is null)
        {
            throw Usage();
        }

        return new ConservativeCommandOptions(
            baselineRoot,
            candidateRoot,
            baselineLeanReport,
            candidateLeanReport);
    }

    private static string RequireDirectory(string path, string label)
    {
        var full = Path.GetFullPath(path);
        return Directory.Exists(full)
            ? full
            : throw new DirectoryNotFoundException($"{label} is absent: {full}");
    }

    private static string RequireFile(string path, string label)
    {
        var full = Path.GetFullPath(path);
        return File.Exists(full)
            ? full
            : throw new FileNotFoundException($"{label} is absent", full);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint verify-conservative "
        + "--baseline-root DIR --candidate-root DIR "
        + "--baseline-lean-report FILE --candidate-lean-report FILE");

    private static ExplicitCommandResult Infrastructure(string message) => new(
        2,
        string.Empty,
        $"INFRASTRUCTURE_FAILURE verify-conservative: {message}\n");

    private static string StrictUtf8(ImmutableArray<byte> bytes) =>
        new UTF8Encoding(false, true).GetString(bytes.AsSpan());

    private sealed record ConservativeCommandOptions(
        string BaselineRoot,
        string CandidateRoot,
        string BaselineLeanReport,
        string CandidateLeanReport);
}

internal sealed class ProductionConservativeExtensionEnvironment : IConservativeExtensionEnvironment
{
    private const string DllRelativePath =
        "Meta/StrataLint/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll";

    private static readonly string[] ProgramFiles =
    [
        "StrataLint.Definitions.dll",
        "StrataLint.Engine.dll",
        "StrataLint.Scribe.dll",
        "StrataLint.deps.json",
        "StrataLint.dll",
        "StrataLint.runtimeconfig.json",
    ];

    public MaterializedConservativeCorpus Materialize(string baselineRoot) =>
        GoldenCorpusMaterializer.Materialize(baselineRoot);

    public ConservativeRepositoryIdentity IdentifyRepository(string root)
    {
        var status = BoundedProcessRunner.Run(
            "git",
            ["status", "--porcelain", "--untracked-files=no"],
            root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);
        if (status.ExitCode != 0)
        {
            throw new InvalidOperationException(
                Encoding.UTF8.GetString(status.StandardError).Trim() is { Length: > 0 } error
                    ? error
                    : "git status failed");
        }

        if (status.StandardOutput.Length != 0)
        {
            throw new InvalidOperationException(
                $"conservative verification requires a clean tracked tree: {root}");
        }

        var frozen = new GitRepositoryGateway(root).ResolveCurrentRevision();
        return new ConservativeRepositoryIdentity(
            frozen.Revision,
            frozen.TreeOid);
    }

    public ConservativeHarnessProgram LoadHarness(string root)
    {
        var dll = Path.Combine(root, DllRelativePath);
        var directory = Path.GetDirectoryName(dll)
            ?? throw new InvalidOperationException("harness DLL path has no directory");
        var files = ProgramFiles.Select(name =>
        {
            var path = Path.Combine(directory, name);
            if (!File.Exists(path)) throw new FileNotFoundException("harness program file is absent", path);
            return new { name, root = FileRoot(path) };
        }).ToArray();
        var canonical = StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(new { files }));
        return new ConservativeHarnessProgram(
            dll,
            GoldenCorpusMaterializer.ContentRoot(canonical.AsSpan()));
    }

    public string FileRoot(string path) =>
        GoldenCorpusMaterializer.ContentRoot(File.ReadAllBytes(path));

    public ConservativeHarnessExecution Execute(ConservativeHarnessInvocation invocation)
    {
        var temporary = Path.Combine(
            Path.GetTempPath(),
            "stratalint-conservative-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(temporary);
        var corpusPath = Path.Combine(temporary, "corpus.json");
        try
        {
            File.WriteAllBytes(corpusPath, invocation.Corpus.CanonicalBytes.AsSpan());
            File.SetAttributes(corpusPath, FileAttributes.ReadOnly);
            var arguments = new[]
            {
                invocation.Program.DllPath,
                "evaluate-conservative-corpus",
                "--corpus", corpusPath,
                "--baseline-root", invocation.BaselineRoot,
                "--candidate-root", invocation.CandidateRoot,
                "--baseline-commit", invocation.BaselineIdentity.CommitOid,
                "--baseline-tree", invocation.BaselineIdentity.TreeOid,
                "--candidate-commit", invocation.CandidateIdentity.CommitOid,
                "--candidate-tree", invocation.CandidateIdentity.TreeOid,
                "--baseline-lean-report", invocation.BaselineLeanReport,
                "--candidate-lean-report", invocation.CandidateLeanReport,
            };
            var process = BoundedProcessRunner.Run(
                "dotnet",
                arguments,
                invocation.BaselineRoot,
                TimeSpan.FromMinutes(3),
                32 * 1024 * 1024);
            var after = FileRoot(corpusPath);
            if (!string.Equals(after, invocation.Corpus.Root, StringComparison.Ordinal))
            {
                return new ConservativeHarnessExecution.InfrastructureFailure(
                    "base-owned corpus changed during harness execution");
            }

            if (process.ExitCode != 0 || process.StandardError.Length != 0)
            {
                var error = Encoding.UTF8.GetString(process.StandardError).Trim();
                return new ConservativeHarnessExecution.InfrastructureFailure(
                    error.Length > 0
                        ? error
                        : $"harness worker exited {process.ExitCode}");
            }

            return new ConservativeHarnessExecution.Completed(
                ConservativeHarnessRunCodec.Read(process.StandardOutput));
        }
        finally
        {
            if (File.Exists(corpusPath)) File.SetAttributes(corpusPath, FileAttributes.Normal);
            Directory.Delete(temporary, recursive: true);
        }
    }
}
