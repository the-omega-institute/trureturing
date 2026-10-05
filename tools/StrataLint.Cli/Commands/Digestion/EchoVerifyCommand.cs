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
            var templatePath = Path.Combine(repositoryRoot, "agents", "echo-template.md");
            var templateFindings = EchoTemplatePolicy.Validate(File.ReadAllText(templatePath, Encoding.UTF8));
            if (templateFindings.Count > 0)
            {
                return new ExplicitCommandResult(
                    1,
                    string.Empty,
                    string.Concat(templateFindings.Select(static finding =>
                        $"ECHO_TEMPLATE_INVALID {finding}\n")));
            }

            var baseRevision = Parse(arguments);
            var prepared = repository.Prepare(baseRevision);
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

    private static string Parse(IReadOnlyList<string> arguments)
    {
        var emit = false;
        string? baseRevision = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--emit" when !emit:
                    emit = true;
                    break;
                case "--base" when baseRevision is null && index + 1 < arguments.Count:
                    baseRevision = arguments[++index];
                    if (string.IsNullOrWhiteSpace(baseRevision)) throw Usage();
                    break;
                default:
                    throw Usage();
            }
        }

        if (!emit || baseRevision is null)
        {
            throw Usage();
        }

        return baseRevision;
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint echo-verify --emit --base REV");
}

internal static class EchoTemplatePolicy
{
    private static readonly string[] RequiredVocabulary =
    [
        "Remark-closure guard",
        "numerical certificate",
        "independently testable identity",
        "upgrade-candidate",
        "retained_residual",
        "unresolved_subitems",
    ];

    internal static IReadOnlyList<string> Validate(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        return RequiredVocabulary
            .Where(term => !text.Contains(term, StringComparison.Ordinal))
            .Select(static term => $"agents/echo-template.md is missing required term '{term}'")
            .ToArray();
    }
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

    private static string ComputeDigest(ReadOnlySpan<byte> residualSummary)
    {
        var preimage = new byte[DigestDomainBytes.Length + residualSummary.Length];
        DigestDomainBytes.CopyTo(preimage, 0);
        residualSummary.CopyTo(preimage.AsSpan(DigestDomainBytes.Length));
        return Convert.ToHexStringLower(SHA256.HashData(preimage));
    }
}
