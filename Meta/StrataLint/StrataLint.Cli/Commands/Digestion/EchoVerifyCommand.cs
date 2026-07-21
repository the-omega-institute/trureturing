using System.Text;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class EchoVerifyCommand
{
    internal static ExplicitCommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = Parse(arguments);
            var prepared = repository.Prepare(options.BaseRevision);
            if (options.IfAffected && !IsAffected(prepared.Changes))
            {
                return new ExplicitCommandResult(0, "ECHO_VERIFY_NOT_APPLICABLE\n", string.Empty);
            }

            var summary = DigestStatusCommand.Run(
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                ["--residual-summary", "--base", prepared.Revision]);
            if (!summary.Success)
            {
                return new ExplicitCommandResult(
                    2,
                    string.Empty,
                    "ECHO_VERIFY_INFRASTRUCTURE residual derivation failed\n" + summary.Error);
            }

            var candidate = repository.ResolveCurrentRevision();
            var baseline = repository.ResolveFrozenRevision(prepared.Revision);
            var expected = EchoResidualBlock.Render(
                summary.Output,
                baseline.CommitOid);
            if (options.Emit)
            {
                return new ExplicitCommandResult(0, expected, string.Empty);
            }

            var filePath = options.FilePath ?? EchoResidualBlock.RelativePath;
            var candidatePath = Path.IsPathRooted(filePath)
                ? filePath
                : Path.Combine(repositoryRoot, filePath);
            byte[] candidateBytes;
            try
            {
                candidateBytes = File.ReadAllBytes(candidatePath);
            }
            catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
            {
                return new ExplicitCommandResult(
                    1,
                    string.Empty,
                    $"ECHO_VERIFY_INVALID candidate file is missing: {candidatePath}\n");
            }

            var error = EchoResidualBlock.Verify(candidateBytes, Encoding.UTF8.GetBytes(expected));
            return error is null
                ? new ExplicitCommandResult(
                    0,
                    $"ECHO_VERIFY_OK candidate={candidate.CommitOid} base={baseline.CommitOid}\n",
                    string.Empty)
                : new ExplicitCommandResult(1, string.Empty, $"ECHO_VERIFY_INVALID {error}\n");
        }
        catch (Exception exception) when (
            exception is FormatException
                or InvalidOperationException
                or IOException
                or ArgumentException)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"ECHO_VERIFY_INFRASTRUCTURE {exception.Message}\n");
        }
    }

    internal static bool IsAffected(RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(changes);
        return changes.Paths.Any(static path =>
            path.Value.StartsWith("D5/", StringComparison.Ordinal)
            || (path.Value.StartsWith("Blueprint/", StringComparison.Ordinal)
                && path.Value.EndsWith(".scribe.cs", StringComparison.Ordinal))
            || path.Value == BackfillInventoryLoader.RelativePath
            || path.Value == EchoResidualBlock.RelativePath
            || DigestionOpaquePathPolicy.IsOpaque(path));
    }

    private static EchoVerifyOptions Parse(IReadOnlyList<string> arguments)
    {
        var emit = false;
        var ifAffected = false;
        string? filePath = null;
        string? baseRevision = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--emit" when !emit && filePath is null:
                    emit = true;
                    break;
                case "--file" when !emit && filePath is null && index + 1 < arguments.Count:
                    filePath = arguments[++index];
                    if (string.IsNullOrWhiteSpace(filePath)) throw Usage();
                    break;
                case "--base" when baseRevision is null && index + 1 < arguments.Count:
                    baseRevision = arguments[++index];
                    if (string.IsNullOrWhiteSpace(baseRevision)) throw Usage();
                    break;
                case "--if-affected" when !ifAffected:
                    ifAffected = true;
                    break;
                default:
                    throw Usage();
            }
        }

        if (baseRevision is null || (emit && (filePath is not null || ifAffected))) throw Usage();
        return new EchoVerifyOptions(emit, filePath, baseRevision, ifAffected);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint echo-verify (--emit|[--file FILE] [--if-affected]) --base REV");

    private sealed record EchoVerifyOptions(
        bool Emit,
        string? FilePath,
        string BaseRevision,
        bool IfAffected);
}

internal static class EchoResidualBlock
{
    internal const string RelativePath = GeneratedArtifactInventory.EchoResidualSummaryPath;
    private const string StartPrefix = "<!-- echo-residual-summary:v2 ";
    private const string EndMarker = "<!-- /echo-residual-summary:v2 -->";
    private static readonly byte[] StartPrefixBytes = Encoding.ASCII.GetBytes(StartPrefix);

    internal static string Render(
        string residualSummary,
        string baseCommitOid)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(residualSummary);
        ArgumentException.ThrowIfNullOrWhiteSpace(baseCommitOid);
        if (!residualSummary.EndsWith('\n'))
        {
            throw new ArgumentException("residual summary must end with LF", nameof(residualSummary));
        }

        return $"{StartPrefix}base={baseCommitOid} -->\n"
            + residualSummary
            + EndMarker
            + "\n";
    }

    internal static string? Verify(ReadOnlySpan<byte> candidate, ReadOnlySpan<byte> expected)
    {
        if (candidate.SequenceEqual(expected))
        {
            return null;
        }

        if (Count(candidate, expected) > 1)
        {
            return "candidate contains multiple echo residual summary blocks";
        }

        if (candidate.IndexOf(StartPrefixBytes) < 0)
        {
            return "candidate contains no echo residual summary block";
        }

        return "candidate block does not byte-match the derived residual summary";
    }

    private static int Count(ReadOnlySpan<byte> source, ReadOnlySpan<byte> value)
    {
        var count = 0;
        while (source.IndexOf(value) is var index && index >= 0)
        {
            count++;
            source = source[(index + value.Length)..];
        }

        return count;
    }
}
