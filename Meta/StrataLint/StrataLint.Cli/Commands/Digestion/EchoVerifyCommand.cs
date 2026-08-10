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
            if (options.CheckStructure)
            {
                // This is an opt-in read-only diagnostic. It is not an admission check,
                // required check, freshness check, or automatic write-back step.
                return CheckStructure(repositoryRoot, DigestStatusCommand.CurrentSourceIds(repository));
            }

            var prepared = repository.Prepare(options.BaseRevision!);
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

            var expected = EchoResidualBlock.Render(summary.Output);
            WriteShards(
                repositoryRoot,
                DigestStatusCommand.RenderShards(
                    repository,
                    leanReportSource,
                    scribeEmissionVerifier,
                    prepared.Revision));
            return new ExplicitCommandResult(0, expected, string.Empty);
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

    internal static ExplicitCommandResult CheckStructure(
        string repositoryRoot,
        IReadOnlyCollection<string> expectedSourceIds)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(expectedSourceIds);
        var legacyPath = Path.Combine(repositoryRoot, "Generated", "echo-residual-summary.md");
        if (File.Exists(legacyPath))
        {
            return StructureInvalid("legacy aggregate exists: Generated/echo-residual-summary.md");
        }

        var directory = Path.Combine(repositoryRoot, "Generated", "echo-residuals");
        if (!Directory.Exists(directory))
        {
            return StructureInvalid("shard directory does not exist: Generated/echo-residuals");
        }

        var expected = expectedSourceIds
            .Select(static sourceId => sourceId + ".md")
            .ToHashSet(StringComparer.Ordinal);
        var actualPaths = Directory.GetFiles(directory, "*.md", SearchOption.TopDirectoryOnly);
        var actual = actualPaths
            .Select(static path => Path.GetFileName(path))
            .ToHashSet(StringComparer.Ordinal);
        var missing = expected.Except(actual, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var extra = actual.Except(expected, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        if (missing.Length > 0 || extra.Length > 0)
        {
            var details = new List<string>();
            if (missing.Length > 0) details.Add("missing=" + string.Join(',', missing));
            if (extra.Length > 0) details.Add("extra=" + string.Join(',', extra));
            return StructureInvalid(string.Join(" ", details));
        }

        foreach (var path in actualPaths.Order(StringComparer.Ordinal))
        {
            var fileName = Path.GetFileName(path);
            var sourceId = Path.GetFileNameWithoutExtension(path);
            var content = File.ReadAllText(path, Encoding.UTF8);
            bool valid;
            try
            {
                valid = EchoResidualBlock.VerifyShard(sourceId, content);
            }
            catch (ArgumentException)
            {
                valid = false;
            }

            if (!valid) return StructureInvalid($"invalid shard {fileName}");
        }

        return new ExplicitCommandResult(0, "ECHO_STRUCTURE_VALID\n", string.Empty);
    }

    private static ExplicitCommandResult StructureInvalid(string reason) =>
        new(1, string.Empty, $"ECHO_STRUCTURE_INVALID {reason}\n");

    private static void WriteShards(
        string repositoryRoot,
        IReadOnlyDictionary<string, string> shards)
    {
        var canonicalDirectory = Path.GetFullPath(
            Path.Combine(repositoryRoot, "Generated", "echo-residuals"));
        Directory.CreateDirectory(canonicalDirectory);
        var expected = new HashSet<string>(StringComparer.Ordinal);
        foreach (var (relativePath, content) in shards)
        {
            if (!RepositoryPathPolicy.IsEchoResidualShardPath(relativePath))
            {
                throw new InvalidOperationException($"noncanonical echo shard path: {relativePath}");
            }

            var destination = Path.GetFullPath(Path.Combine(repositoryRoot, relativePath));
            if (!string.Equals(Path.GetDirectoryName(destination), canonicalDirectory, StringComparison.Ordinal))
            {
                throw new InvalidOperationException($"echo shard escaped canonical directory: {relativePath}");
            }

            expected.Add(destination);
            File.WriteAllText(destination, content, new UTF8Encoding(false));
        }

        foreach (var existing in Directory.GetFiles(canonicalDirectory, "*.md", SearchOption.TopDirectoryOnly))
        {
            if (!expected.Contains(existing)) File.Delete(existing);
        }
    }

    private static EchoVerifyOptions Parse(IReadOnlyList<string> arguments)
    {
        var emit = false;
        var checkStructure = false;
        string? baseRevision = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--emit" when !emit:
                    emit = true;
                    break;
                case "--check-structure" when !checkStructure:
                    checkStructure = true;
                    break;
                case "--base" when baseRevision is null && index + 1 < arguments.Count:
                    baseRevision = arguments[++index];
                    if (string.IsNullOrWhiteSpace(baseRevision)) throw Usage();
                    break;
                default:
                    throw Usage();
            }
        }

        if (emit == checkStructure || (emit && baseRevision is null) || (checkStructure && baseRevision is not null))
        {
            throw Usage();
        }

        return new EchoVerifyOptions(emit, checkStructure, baseRevision);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint echo-verify (--emit --base REV | --check-structure); "
        + "--check-structure is an opt-in read-only diagnostic, not an admission or required check");

    private sealed record EchoVerifyOptions(bool Emit, bool CheckStructure, string? BaseRevision);
}

internal static class EchoResidualBlock
{
    private const string DigestDomain = "stratalint.echo-residual-summary.v3\0";
    private const string StartPrefix = "<!-- echo-residual-summary:v3 residual=sha256:";
    private const string HeaderSuffix = " -->";
    private static readonly byte[] DigestDomainBytes = Encoding.ASCII.GetBytes(DigestDomain);
    private const string ShardDigestDomain = "stratalint.echo-residual-summary.v4\0";
    private const string ShardStartPrefix = "<!-- echo-residual-summary:v4 source=";

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

    internal static string RenderShard(string sourceId, string body)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(sourceId);
        ArgumentException.ThrowIfNullOrWhiteSpace(body);
        if (!body.EndsWith('\n')) throw new ArgumentException("shard body must end with LF", nameof(body));
        var preimage = Encoding.UTF8.GetBytes(ShardDigestDomain + sourceId + "\0" + body);
        var digest = Convert.ToHexStringLower(SHA256.HashData(preimage));
        return $"{ShardStartPrefix}{sourceId} residual=sha256:{digest}{HeaderSuffix}\n{body}";
    }

    internal static bool VerifyShard(string sourceId, string content)
    {
        var newline = content.IndexOf('\n');
        return newline >= 0
            && string.Equals(RenderShard(sourceId, content[(newline + 1)..]), content, StringComparison.Ordinal);
    }

    private static string ComputeDigest(ReadOnlySpan<byte> residualSummary)
    {
        var preimage = new byte[DigestDomainBytes.Length + residualSummary.Length];
        DigestDomainBytes.CopyTo(preimage, 0);
        residualSummary.CopyTo(preimage.AsSpan(DigestDomainBytes.Length));
        return Convert.ToHexStringLower(SHA256.HashData(preimage));
    }
}
