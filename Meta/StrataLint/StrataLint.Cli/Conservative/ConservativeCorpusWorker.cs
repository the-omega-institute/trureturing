using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Cli;

internal static class ConservativeCorpusWorker
{
    internal static ExplicitCommandResult Run(IReadOnlyList<string> arguments)
    {
        try
        {
            var options = Parse(arguments);
            var environment = new ProductionConservativeExtensionEnvironment();
            var baselineIdentity = environment.IdentifyRepository(options.BaselineRoot);
            var candidateIdentity = environment.IdentifyRepository(options.CandidateRoot);
            RequireIdentity("baseline", baselineIdentity, options.BaselineCommit, options.BaselineTree);
            RequireIdentity("candidate", candidateIdentity, options.CandidateCommit, options.CandidateTree);

            var loadedAssembly = Path.GetFullPath(typeof(Program).Assembly.Location);
            var baselineProgram = environment.LoadHarness(options.BaselineRoot);
            var candidateProgram = environment.LoadHarness(options.CandidateRoot);
            var program = string.Equals(
                loadedAssembly,
                Path.GetFullPath(baselineProgram.DllPath),
                StringComparison.Ordinal)
                ? baselineProgram
                : string.Equals(
                    loadedAssembly,
                    Path.GetFullPath(candidateProgram.DllPath),
                    StringComparison.Ordinal)
                    ? candidateProgram
                    : throw new InvalidOperationException(
                        "loaded harness does not belong to either supplied repository root");
            var corpusBytes = ImmutableArray.CreateRange(File.ReadAllBytes(options.CorpusPath));
            var corpus = new MaterializedConservativeCorpus(
                corpusBytes,
                GoldenCorpusMaterializer.ContentRoot(corpusBytes.AsSpan()),
                ImmutableArray<string>.Empty);
            var invocation = new ConservativeHarnessInvocation(
                program,
                corpus,
                options.BaselineRoot,
                options.CandidateRoot,
                baselineIdentity,
                candidateIdentity,
                options.BaselineLeanReport,
                options.CandidateLeanReport);
            var synthetic = ConservativeCorpusEvaluator.Evaluate(corpusBytes.AsSpan(), program.Root);
            var cases = synthetic.Cases
                .Add(ConservativeActualTreeEvaluator.EvaluateBaselineTree(invocation))
                .Add(ConservativeActualTreeEvaluator.EvaluateCandidateTree(invocation));
            var run = synthetic with { Cases = cases };
            var output = ConservativeHarnessRunCodec.Write(run);
            return new ExplicitCommandResult(
                0,
                new UTF8Encoding(false, true).GetString(output.AsSpan()),
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"INFRASTRUCTURE_FAILURE evaluate-conservative-corpus: {exception.Message}\n");
        }
    }

    private static WorkerOptions Parse(IReadOnlyList<string> arguments)
    {
        var values = new Dictionary<string, string>(StringComparer.Ordinal);
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count
                || arguments[index] is not (
                    "--corpus"
                    or "--baseline-root"
                    or "--candidate-root"
                    or "--baseline-commit"
                    or "--baseline-tree"
                    or "--candidate-commit"
                    or "--candidate-tree"
                    or "--baseline-lean-report"
                    or "--candidate-lean-report")
                || !values.TryAdd(arguments[index], arguments[index + 1]))
            {
                throw Usage();
            }
        }

        if (values.Count != 9) throw Usage();
        return new WorkerOptions(
            RequireFile(values["--corpus"], "corpus"),
            RequireDirectory(values["--baseline-root"], "baseline root"),
            RequireDirectory(values["--candidate-root"], "candidate root"),
            values["--baseline-commit"],
            values["--baseline-tree"],
            values["--candidate-commit"],
            values["--candidate-tree"],
            RequireFile(values["--baseline-lean-report"], "baseline Lean report"),
            RequireFile(values["--candidate-lean-report"], "candidate Lean report"));
    }

    private static void RequireIdentity(
        string side,
        ConservativeRepositoryIdentity actual,
        string commit,
        string tree)
    {
        if (!string.Equals(actual.CommitOid, commit, StringComparison.Ordinal)
            || !string.Equals(actual.TreeOid, tree, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"{side} repository identity changed before replay");
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
        "USAGE: StrataLint evaluate-conservative-corpus "
        + "--corpus FILE --baseline-root DIR --candidate-root DIR "
        + "--baseline-commit OID --baseline-tree OID "
        + "--candidate-commit OID --candidate-tree OID "
        + "--baseline-lean-report FILE --candidate-lean-report FILE");

    private sealed record WorkerOptions(
        string CorpusPath,
        string BaselineRoot,
        string CandidateRoot,
        string BaselineCommit,
        string BaselineTree,
        string CandidateCommit,
        string CandidateTree,
        string BaselineLeanReport,
        string CandidateLeanReport);
}
