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

    private static EchoVerifyOptions Parse(IReadOnlyList<string> arguments)
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

        if (!emit || baseRevision is null) throw Usage();
        return new EchoVerifyOptions(baseRevision);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint echo-verify --emit --base REV");

    private sealed record EchoVerifyOptions(string BaseRevision);
}

internal static class EchoResidualBlock
{
    internal const string RelativePath = GeneratedArtifactInventory.EchoResidualSummaryPath;
    private const string DigestDomain = "stratalint.echo-residual-summary.v3\0";
    private const string StartPrefix = "<!-- echo-residual-summary:v3 residual=sha256:";
    private const string HeaderSuffix = " -->";
    private static readonly byte[] DigestDomainBytes = Encoding.ASCII.GetBytes(DigestDomain);

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

    private static string ComputeDigest(ReadOnlySpan<byte> residualSummary)
    {
        var preimage = new byte[DigestDomainBytes.Length + residualSummary.Length];
        DigestDomainBytes.CopyTo(preimage, 0);
        residualSummary.CopyTo(preimage.AsSpan(DigestDomainBytes.Length));
        return Convert.ToHexStringLower(SHA256.HashData(preimage));
    }
}
