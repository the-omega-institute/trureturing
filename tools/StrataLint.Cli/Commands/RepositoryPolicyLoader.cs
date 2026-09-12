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
            return new PolicyLoadOutcome.Accepted(ValidatedPolicy.Create(
                FileMapLoader.Parse(fileMapBytes, FileMapLoader.RelativePath), DomainsLoader.Parse(domainsBytes)));
        }
        catch (Exception exception) when (exception is DecoderFallbackException or YamlException or FormatException)
        {
            return new PolicyLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }
}
