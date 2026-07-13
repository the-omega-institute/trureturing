using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Cli;

internal static class ConservativeCorpusWorker
{
    private const int MaximumEnvelopeBytes = 128 * 1024 * 1024;

    internal static ExplicitCommandResult Run(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 0) throw Usage();
            var replay = ConservativeReplayEnvelopeCodec.Read(ReadStandardInput().AsSpan());
            var loadedAssembly = Path.GetFullPath(typeof(Program).Assembly.Location);
            var program = ProductionConservativeExtensionEnvironment.LoadHarnessAssembly(
                loadedAssembly);
            using var workspace = ConservativeReplayWorkspace.Materialize(replay);
            var invocation = new ConservativeHarnessInvocation(
                program,
                replay,
                replay.Corpus,
                workspace.BaselineRoot,
                workspace.CandidateRoot,
                replay.BaselineIdentity,
                replay.CandidateIdentity,
                workspace.BaselineLeanReport,
                workspace.CandidateLeanReport);
            var synthetic = ConservativeCorpusEvaluator.Evaluate(
                replay.Corpus.CanonicalBytes.AsSpan(),
                program.Root);
            var cases = synthetic.Cases
                .Add(ConservativeActualTreeEvaluator.EvaluateBaselineTree(invocation))
                .Add(ConservativeActualTreeEvaluator.EvaluateCandidateTree(invocation));
            var output = ConservativeHarnessRunCodec.Write(synthetic with { Cases = cases });
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

    private static ImmutableArray<byte> ReadStandardInput()
    {
        using var input = Console.OpenStandardInput();
        using var memory = new MemoryStream();
        var buffer = new byte[8192];
        while (true)
        {
            var count = input.Read(buffer, 0, buffer.Length);
            if (count == 0) break;
            if (memory.Length + count > MaximumEnvelopeBytes)
            {
                throw new InvalidOperationException(
                    $"conservative replay envelope exceeds {MaximumEnvelopeBytes} bytes");
            }

            memory.Write(buffer, 0, count);
        }

        return ImmutableArray.CreateRange(memory.ToArray());
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint evaluate-conservative-corpus < replay-envelope.json");
}
