using System.Security.Cryptography;
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
            var expected = EchoResidualBlock.Render(summary.Output);
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
    private const string DigestDomain = "stratalint.echo-residual-summary.v3\0";
    private const string MarkerPrefix = "<!-- echo-residual-summary:";
    private const string StartPrefix = "<!-- echo-residual-summary:v3 residual=sha256:";
    private const string HeaderSuffix = " -->";
    private const int Sha256HexLength = 64;
    private static readonly byte[] DigestDomainBytes = Encoding.ASCII.GetBytes(DigestDomain);
    private static readonly byte[] HeaderSuffixBytes = Encoding.ASCII.GetBytes(HeaderSuffix);
    private static readonly byte[] MarkerPrefixBytes = Encoding.ASCII.GetBytes(MarkerPrefix);
    private static readonly byte[] StartPrefixBytes = Encoding.ASCII.GetBytes(StartPrefix);

    internal static string Render(string residualSummary)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(residualSummary);
        if (!residualSummary.EndsWith('\n'))
        {
            throw new ArgumentException("residual summary must end with LF", nameof(residualSummary));
        }

        var body = Encoding.UTF8.GetBytes(residualSummary);
        return $"{StartPrefix}{ComputeDigest(body)}{HeaderSuffix}\n" + residualSummary;
    }

    internal static string? Verify(ReadOnlySpan<byte> candidate, ReadOnlySpan<byte> expected)
    {
        var markerCount = Count(candidate, MarkerPrefixBytes);
        if (markerCount > 1)
        {
            return "candidate contains multiple echo residual summary blocks";
        }

        if (markerCount == 0)
        {
            return "candidate contains no echo residual summary block";
        }

        if (!TrySplit(candidate, out var candidateDigest, out _)
            || !TrySplit(expected, out _, out var expectedBody))
        {
            return "candidate contains malformed echo residual summary marker";
        }

        if (!candidateDigest.SequenceEqual(Encoding.ASCII.GetBytes(ComputeDigest(expectedBody))))
        {
            return "candidate block does not byte-match the derived residual summary";
        }

        return candidate.SequenceEqual(expected)
            ? null
            : "candidate block does not byte-match the derived residual summary";
    }

    private static bool TrySplit(
        ReadOnlySpan<byte> value,
        out ReadOnlySpan<byte> digest,
        out ReadOnlySpan<byte> body)
    {
        digest = default;
        body = default;
        var lineFeed = value.IndexOf((byte)'\n');
        if (lineFeed < 0 || !value.StartsWith(StartPrefixBytes)) return false;

        var header = value[..lineFeed];
        var expectedHeaderLength = StartPrefixBytes.Length + Sha256HexLength + HeaderSuffix.Length;
        if (header.Length != expectedHeaderLength
            || !header.EndsWith(HeaderSuffixBytes))
        {
            return false;
        }

        digest = header.Slice(StartPrefixBytes.Length, Sha256HexLength);
        foreach (var valueByte in digest)
        {
            if (valueByte is not (>= (byte)'0' and <= (byte)'9')
                and not (>= (byte)'a' and <= (byte)'f'))
            {
                return false;
            }
        }

        body = value[(lineFeed + 1)..];
        return true;
    }

    private static string ComputeDigest(ReadOnlySpan<byte> residualSummary)
    {
        var preimage = new byte[DigestDomainBytes.Length + residualSummary.Length];
        DigestDomainBytes.CopyTo(preimage, 0);
        residualSummary.CopyTo(preimage.AsSpan(DigestDomainBytes.Length));
        return Convert.ToHexStringLower(SHA256.HashData(preimage));
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
