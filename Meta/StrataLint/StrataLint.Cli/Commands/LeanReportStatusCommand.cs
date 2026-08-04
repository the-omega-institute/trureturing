using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LeanReportStatusCommand
{
    internal static ExplicitCommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        if (arguments.Count != 0)
        {
            return NotChecked("USAGE: StrataLint lean-report-status");
        }

        RepositorySnapshot snapshot;
        try
        {
            snapshot = SnapshotDecoder.Decode(repository.ReadCurrent()) switch
            {
                SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
                SnapshotDecodeOutcome.InfrastructureFailure failure =>
                    throw new InvalidOperationException(failure.Message),
            };
        }
        catch (Exception exception)
        {
            return NotChecked(exception.Message);
        }

        try
        {
            _ = leanReportSource.Load(snapshot);
            return new ExplicitCommandResult(0, "LEAN_REPORT_STATUS valid\n", string.Empty);
        }
        catch (Exception exception) when (
            exception is FormatException
                or DecoderFallbackException
                or FileNotFoundException
                or DirectoryNotFoundException)
        {
            return new ExplicitCommandResult(
                1,
                $"LEAN_REPORT_STATUS invalid {SingleLine(exception.Message)}\n",
                string.Empty);
        }
        catch (Exception exception)
        {
            return NotChecked(exception.Message);
        }
    }

    private static ExplicitCommandResult NotChecked(string detail) => new(
        2,
        string.Empty,
        $"LEAN_REPORT_STATUS not-checked {SingleLine(detail)}\n");

    private static string SingleLine(string value) =>
        value.Replace('\r', ' ').Replace('\n', ' ');
}
