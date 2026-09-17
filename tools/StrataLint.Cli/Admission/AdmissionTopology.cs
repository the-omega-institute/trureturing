using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal abstract record AdmissionTopologyOutcome
{
    private AdmissionTopologyOutcome() { }

    internal sealed record BootstrapNotActive(string DefaultBranch) : AdmissionTopologyOutcome;

    internal sealed record SteadyStateActive(string DefaultBranch) : AdmissionTopologyOutcome;

    internal sealed record InfrastructureFailure(string Message) : AdmissionTopologyOutcome;
}

internal static class AdmissionWorkflowTopology
{
    internal const string WorkflowPath = RepositoryPathPolicy.PrWorkflowPath;

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static bool HasRequiredBaseGate(ReadOnlySpan<byte> bytes, string defaultBranch)
    {
        try
        {
            return CiWorkflowDocument.Parse(StrictUtf8.GetString(bytes))?.HasDeltaGate(defaultBranch) == true;
        }
        catch (DecoderFallbackException)
        {
            return false;
        }
    }
}
