using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record ConservativeRepositoryIdentity(string CommitOid, string TreeOid);

internal sealed record ConservativeHarnessProgram(string DllPath, string Root);

internal sealed record ConservativeHarnessInvocation(
    ConservativeHarnessProgram Program,
    ConservativeReplayEnvelope Replay,
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

    ConservativeHarnessProgram LoadHarness(string path);

    ContractEpochStore LoadContractEpoch(
        string root,
        ConservativeRepositoryIdentity identity);

    ConservativeReplayEnvelope Freeze(
        string baselineRoot,
        string candidateRoot,
        ConservativeRepositoryIdentity baselineIdentity,
        ConservativeRepositoryIdentity candidateIdentity,
        string baselineLeanReport,
        string candidateLeanReport,
        MaterializedConservativeCorpus corpus);

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
            var baselineContract = environment.LoadContractEpoch(
                options.BaselineRoot,
                baselineIdentity);
            var candidateContract = environment.LoadContractEpoch(
                options.CandidateRoot,
                candidateIdentity);
            var baselineProgram = environment.LoadHarness(options.BaselineHarness);
            var candidateProgram = environment.LoadHarness(options.CandidateHarness);
            var baselineLeanReportRoot = environment.FileRoot(options.BaselineLeanReport);
            var candidateLeanReportRoot = environment.FileRoot(options.CandidateLeanReport);
            var replay = environment.Freeze(
                options.BaselineRoot,
                options.CandidateRoot,
                baselineIdentity,
                candidateIdentity,
                options.BaselineLeanReport,
                options.CandidateLeanReport,
                corpus);
            RequireFrozenReplay(
                replay,
                corpus,
                baselineIdentity,
                candidateIdentity,
                baselineLeanReportRoot,
                candidateLeanReportRoot);
            var invocation = new ConservativeHarnessInvocation(
                baselineProgram,
                replay,
                corpus,
                options.BaselineRoot,
                options.CandidateRoot,
                baselineIdentity,
                candidateIdentity,
                options.BaselineLeanReport,
                options.CandidateLeanReport);
            var baselineExecution = environment.Execute(invocation);
            RequireFrozenInputs(
                environment,
                options,
                baselineIdentity,
                candidateIdentity,
                baselineProgram,
                candidateProgram,
                baselineLeanReportRoot,
                candidateLeanReportRoot);
            var candidateExecution = environment.Execute(invocation with { Program = candidateProgram });
            RequireFrozenInputs(
                environment,
                options,
                baselineIdentity,
                candidateIdentity,
                baselineProgram,
                candidateProgram,
                baselineLeanReportRoot,
                candidateLeanReportRoot);
            var input = new ConservativeVerificationInput(
                baselineIdentity.CommitOid,
                baselineIdentity.TreeOid,
                candidateIdentity.CommitOid,
                candidateIdentity.TreeOid,
                baselineProgram.Root,
                candidateProgram.Root,
                baselineLeanReportRoot,
                candidateLeanReportRoot,
                corpus.Root,
                replay.Root,
                corpus.CaseIds.Add(BaseTreeCaseId),
                corpus.CaseIds.Length,
                BaseTreeCaseId,
                CandidateTreeCaseId,
                baselineExecution,
                candidateExecution)
            {
                BaselineContractLedger = baselineContract.Ledger,
                CandidateContractLedger = candidateContract.Ledger,
                BaselineContractEvidence = baselineContract.EvidenceWithCustodiansFrom(
                    candidateContract),
                CandidateContractEvidence = candidateContract.EvidenceWithCustodiansFrom(
                    candidateContract),
                ContractExpectations = corpus.ContractExpectations,
            };
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

    private static void RequireFrozenReplay(
        ConservativeReplayEnvelope replay,
        MaterializedConservativeCorpus corpus,
        ConservativeRepositoryIdentity baselineIdentity,
        ConservativeRepositoryIdentity candidateIdentity,
        string baselineLeanReportRoot,
        string candidateLeanReportRoot)
    {
        if (replay.BaselineIdentity != baselineIdentity
            || replay.CandidateIdentity != candidateIdentity
            || !string.Equals(replay.Corpus.Root, corpus.Root, StringComparison.Ordinal)
            || !replay.Corpus.CaseIds.SequenceEqual(corpus.CaseIds, StringComparer.Ordinal)
            || !SameContractExpectations(
                replay.Corpus.ContractExpectations,
                corpus.ContractExpectations)
            || !string.Equals(
                GoldenCorpusMaterializer.ContentRoot(replay.BaselineLeanReport.AsSpan()),
                baselineLeanReportRoot,
                StringComparison.Ordinal)
            || !string.Equals(
                GoldenCorpusMaterializer.ContentRoot(replay.CandidateLeanReport.AsSpan()),
                candidateLeanReportRoot,
                StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "base-owned replay envelope does not match the frozen inputs");
        }
    }

    private static bool SameContractExpectations(
        IReadOnlyDictionary<string, ImmutableArray<string>> left,
        IReadOnlyDictionary<string, ImmutableArray<string>> right) =>
        left.Count == right.Count
        && left.All(item => right.TryGetValue(item.Key, out var expected)
            && item.Value.SequenceEqual(expected, StringComparer.Ordinal));

    private static void RequireFrozenInputs(
        IConservativeExtensionEnvironment environment,
        ConservativeCommandOptions options,
        ConservativeRepositoryIdentity baselineIdentity,
        ConservativeRepositoryIdentity candidateIdentity,
        ConservativeHarnessProgram baselineProgram,
        ConservativeHarnessProgram candidateProgram,
        string baselineLeanReportRoot,
        string candidateLeanReportRoot)
    {
        if (environment.IdentifyRepository(options.BaselineRoot) != baselineIdentity
            || environment.IdentifyRepository(options.CandidateRoot) != candidateIdentity)
        {
            throw new InvalidOperationException(
                "repository identity changed during conservative replay");
        }

        if (!string.Equals(
                environment.FileRoot(options.BaselineLeanReport),
                baselineLeanReportRoot,
                StringComparison.Ordinal)
            || !string.Equals(
                environment.FileRoot(options.CandidateLeanReport),
                candidateLeanReportRoot,
                StringComparison.Ordinal))
        {
            throw new InvalidOperationException("Lean report changed during conservative replay");
        }

        if (environment.LoadHarness(options.BaselineHarness) != baselineProgram
            || environment.LoadHarness(options.CandidateHarness) != candidateProgram)
        {
            throw new InvalidOperationException("harness program changed during conservative replay");
        }
    }

    private static ConservativeCommandOptions Parse(IReadOnlyList<string> arguments)
    {
        string? baselineRoot = null;
        string? candidateRoot = null;
        string? baselineLeanReport = null;
        string? candidateLeanReport = null;
        string? baselineHarness = null;
        string? candidateHarness = null;
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
                case "--baseline-harness" when baselineHarness is null:
                    baselineHarness = RequireFile(value, "baseline harness");
                    break;
                case "--candidate-harness" when candidateHarness is null:
                    candidateHarness = RequireFile(value, "candidate harness");
                    break;
                default:
                    throw Usage();
            }
        }

        if (baselineRoot is null
            || candidateRoot is null
            || baselineLeanReport is null
            || candidateLeanReport is null
            || baselineHarness is null
            || candidateHarness is null)
        {
            throw Usage();
        }

        RequireWithinRoot(baselineHarness, baselineRoot, "baseline harness", "baseline root");
        RequireWithinRoot(candidateHarness, candidateRoot, "candidate harness", "candidate root");

        return new ConservativeCommandOptions(
            baselineRoot,
            candidateRoot,
            baselineLeanReport,
            candidateLeanReport,
            baselineHarness,
            candidateHarness);
    }

    private static void RequireWithinRoot(
        string path,
        string root,
        string pathLabel,
        string rootLabel)
    {
        var relative = Path.GetRelativePath(root, path);
        if (Path.IsPathRooted(relative)
            || string.Equals(relative, "..", StringComparison.Ordinal)
            || relative.StartsWith("../", StringComparison.Ordinal)
            || relative.StartsWith("..\\", StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"{pathLabel} must be within {rootLabel}: {path}");
        }
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
        + "--baseline-lean-report FILE --candidate-lean-report FILE "
        + "--baseline-harness FILE --candidate-harness FILE");

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
        string CandidateLeanReport,
        string BaselineHarness,
        string CandidateHarness);
}

internal sealed class ProductionConservativeExtensionEnvironment : IConservativeExtensionEnvironment
{
    public MaterializedConservativeCorpus Materialize(string baselineRoot) =>
        GoldenCorpusMaterializer.Materialize(baselineRoot);

    public ConservativeRepositoryIdentity IdentifyRepository(string root)
    {
        var status = BoundedProcessRunner.Run(
            "git",
            ["status", "--porcelain", "--untracked-files=all"],
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

    public ConservativeHarnessProgram LoadHarness(string path) => LoadHarnessAssembly(path);

    public ContractEpochStore LoadContractEpoch(
        string root,
        ConservativeRepositoryIdentity identity)
    {
        ArgumentNullException.ThrowIfNull(identity);
        var repository = new GitRepositoryGateway(root);
        var frozen = repository.ResolveFrozenRevision(identity.CommitOid);
        if (!string.Equals(frozen.Revision, identity.CommitOid, StringComparison.Ordinal)
            || !string.Equals(frozen.TreeOid, identity.TreeOid, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "contract epoch store identity does not match its exact repository commit");
        }

        var snapshot = SnapshotDecoder.Decode(repository.ReadRevision(identity.CommitOid)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
        return ContractEpochStore.Load(snapshot);
    }

    internal static ConservativeHarnessProgram LoadHarnessAssembly(string dll)
    {
        dll = Path.GetFullPath(dll);
        var directory = Path.GetDirectoryName(dll)
            ?? throw new InvalidOperationException("harness DLL path has no directory");
        var files = RuntimeProgramFiles(directory).Select(name =>
        {
            var path = Path.Combine(directory, name);
            if (!File.Exists(path)) throw new FileNotFoundException("harness program file is absent", path);
            return new
            {
                name,
                root = GoldenCorpusMaterializer.ContentRoot(File.ReadAllBytes(path)),
            };
        }).ToArray();
        var canonical = StructuredCanonicalWriter.WriteJson(
            JsonSerializer.SerializeToElement(new { files }));
        return new ConservativeHarnessProgram(
            dll,
            GoldenCorpusMaterializer.ContentRoot(canonical.AsSpan()));
    }

    private static ImmutableArray<string> RuntimeProgramFiles(string directory)
    {
        const string depsName = "StrataLint.deps.json";
        const string runtimeConfigName = "StrataLint.runtimeconfig.json";
        var depsPath = Path.Combine(directory, depsName);
        if (!File.Exists(depsPath))
        {
            throw new FileNotFoundException("harness dependency manifest is absent", depsPath);
        }

        using var document = JsonDocument.Parse(File.ReadAllBytes(depsPath));
        var targets = document.RootElement.GetProperty("targets");
        var target = targets.EnumerateObject().Single().Value;
        var names = target.EnumerateObject()
            .SelectMany(static library =>
                library.Value.TryGetProperty("runtime", out var runtime)
                    ? runtime.EnumerateObject().Select(static asset => asset.Name)
                    : Enumerable.Empty<string>())
            .Select(static asset => Path.GetFileName(asset))
            .Append(depsName)
            .Append(runtimeConfigName)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        if (names.IsDefaultOrEmpty
            || !names.Contains("StrataLint.dll", StringComparer.Ordinal)
            || names.Any(static name => string.IsNullOrWhiteSpace(name)
                || !string.Equals(name, Path.GetFileName(name), StringComparison.Ordinal)))
        {
            throw new InvalidOperationException("harness dependency manifest has an invalid runtime closure");
        }

        return names;
    }

    public string FileRoot(string path) =>
        GoldenCorpusMaterializer.ContentRoot(File.ReadAllBytes(path));

    public ConservativeReplayEnvelope Freeze(
        string baselineRoot,
        string candidateRoot,
        ConservativeRepositoryIdentity baselineIdentity,
        ConservativeRepositoryIdentity candidateIdentity,
        string baselineLeanReport,
        string candidateLeanReport,
        MaterializedConservativeCorpus corpus)
    {
        var candidateRepository = new GitRepositoryGateway(candidateRoot);
        var embeddedBaseline = candidateRepository.ResolveFrozenRevision(baselineIdentity.CommitOid);
        if (!string.Equals(
                embeddedBaseline.Revision,
                baselineIdentity.CommitOid,
                StringComparison.Ordinal)
            || !string.Equals(
                embeddedBaseline.TreeOid,
                baselineIdentity.TreeOid,
                StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "candidate object database does not contain the frozen baseline identity");
        }

        var ledger = candidateRepository.ReadRevisionFile(
            candidateIdentity.CommitOid,
            FrozenLedgerChangeClassifier.LedgerPath);
        var loaded = DagLedgerLoader.Load(ledger.Bytes.AsSpan()) switch
        {
            DagLedgerLoadOutcome.Loaded accepted => accepted.Syntax,
            DagLedgerLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                "candidate frozen ledger syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown frozen ledger load outcome"),
        };
        var references = FrozenLedger.ScanReferences(loaded) switch
        {
            FrozenLedgerReferenceScanOutcome.Accepted accepted => accepted.References,
            FrozenLedgerReferenceScanOutcome.Rejected rejected => throw new InvalidOperationException(
                "candidate frozen ledger references are invalid: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown frozen ledger reference outcome"),
        };
        var evidenceCommits = references.CommitOids.Select(static oid =>
            oid[(oid.IndexOf(':') + 1)..]);
        var bundle = ConservativeRepositoryBundle.Create(
            baselineRoot,
            candidateRoot,
            baselineIdentity,
            candidateIdentity,
            evidenceCommits);
        return ConservativeReplayEnvelopeCodec.Create(
            corpus,
            baselineIdentity,
            candidateIdentity,
            File.ReadAllBytes(baselineLeanReport),
            File.ReadAllBytes(candidateLeanReport),
            bundle);
    }

    // 预算默认 180s(历史行为);本机在与其它工作负载共存时 corpus 评估可超 180s
    // (2026-07-19 九次 ceremony 实证,load 6–40 均超时),允许经
    // STRATALINT_CONSERVATIVE_TIMEOUT_SECONDS 显式上调,夹在 [180, 3600] 内。
    private static TimeSpan EvaluationBudget
    {
        get
        {
            var raw = Environment.GetEnvironmentVariable("STRATALINT_CONSERVATIVE_TIMEOUT_SECONDS");
            if (int.TryParse(raw, System.Globalization.NumberStyles.Integer, System.Globalization.CultureInfo.InvariantCulture, out var seconds))
            {
                return TimeSpan.FromSeconds(Math.Clamp(seconds, 180, 3600));
            }

            return TimeSpan.FromMinutes(3);
        }
    }

    public ConservativeHarnessExecution Execute(ConservativeHarnessInvocation invocation)
    {
        var temporary = Path.Combine(
            Path.GetTempPath(),
            "stratalint-conservative-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(temporary);
        try
        {
            var arguments = new[]
            {
                invocation.Program.DllPath,
                "evaluate-conservative-corpus",
            };
            var process = BoundedProcessRunner.Run(
                "dotnet",
                arguments,
                temporary,
                EvaluationBudget,
                32 * 1024 * 1024,
                invocation.Replay.CanonicalBytes.AsMemory());
            var after = ConservativeReplayEnvelopeCodec.Read(
                invocation.Replay.CanonicalBytes.AsSpan());
            if (!string.Equals(after.Root, invocation.Replay.Root, StringComparison.Ordinal))
            {
                return new ConservativeHarnessExecution.InfrastructureFailure(
                    "base-owned replay envelope changed during harness execution");
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
            Directory.Delete(temporary, recursive: true);
        }
    }
}
