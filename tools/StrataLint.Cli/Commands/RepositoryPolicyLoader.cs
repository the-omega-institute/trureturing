using System.Text;
using StrataLint.Engine;
using YamlDotNet.Core;

namespace StrataLint.Cli;

public static class RepositoryPolicyLoader
{
    public static PolicyLoadOutcome Load(ReadOnlySpan<byte> fileMapBytes, ReadOnlySpan<byte> domainsBytes)
    {
        try
        {
            return Load(FileMapLoader.Parse(fileMapBytes, FileMapLoader.RelativePath), domainsBytes);
        }
        catch (Exception exception) when (IsPolicyFailure(exception))
        {
            return new PolicyLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }

    internal static PolicyLoadOutcome LoadRepository(string repositoryRoot)
    {
        try
        {
            return Load(
                FileMapLoader.LoadRepository(repositoryRoot),
                File.ReadAllBytes(Path.Combine(repositoryRoot, "Meta/domains.yaml")));
        }
        catch (Exception exception) when (IsPolicyFailure(exception))
        {
            return new PolicyLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }

    internal static PolicyLoadOutcome Load(RepositorySnapshot snapshot)
    {
        try
        {
            if (!snapshot.TryGetFile("Meta/domains.yaml", out var domains))
            {
                throw new FormatException("current snapshot lacks Meta/domains.yaml");
            }

            return Load(FileMapLoader.LoadSnapshot(snapshot), domains.RawBytes.AsSpan());
        }
        catch (Exception exception) when (IsPolicyFailure(exception))
        {
            return new PolicyLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }

    internal static PolicyLoadOutcome Load(FileMapManifest manifest, ReadOnlySpan<byte> domainsBytes)
    {
        try
        {
            return new PolicyLoadOutcome.Accepted(ValidatedPolicy.Create(
                manifest, DomainsLoader.Parse(domainsBytes)));
        }
        catch (Exception exception) when (IsPolicyFailure(exception))
        {
            return new PolicyLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }

    private static bool IsPolicyFailure(Exception exception) =>
        exception is DecoderFallbackException or YamlException or FormatException
            or IOException or UnauthorizedAccessException;
}
