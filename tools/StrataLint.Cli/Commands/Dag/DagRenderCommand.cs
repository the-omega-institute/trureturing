using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;

namespace StrataLint.Cli;

/// Projects the repository truth DAG to Generated/DAG.md.
///
/// The graph is built here rather than in Scribe because only this assembly holds the repository
/// gateway that produces a RepositorySnapshot; the rendering itself belongs to Scribe, which owns
/// every other canonical projection. Failures are classified the same way the ledger commands
/// classify them: an unreadable repository or an unusable Lean report is an environment fault, not
/// a verdict about the graph.
internal static class DagRenderCommand
{
    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);

        var check = false;
        foreach (var argument in arguments)
        {
            if (argument == "--check")
            {
                check = true;
                continue;
            }

            return new CommandResult(
                false,
                string.Empty,
                $"dag-render: unknown argument {argument}\nusage: dag-render [--check]\n");
        }

        TruthContext truth;
        try
        {
            truth = DagLedgerCommandPreparation.BuildTruth(repository, leanReportSource);
        }
        catch (DagLedgerCommandPreparation.RepositoryUnavailableException exception)
        {
            return Failure("repository could not be read", exception);
        }
        catch (DagLedgerCommandPreparation.LeanReportUnusableException exception)
        {
            return Failure("raw Lean report is unusable", exception);
        }
        catch (InvalidOperationException exception)
        {
            return Failure("truth DAG could not be built", exception);
        }

        var output = new StringWriter();
        var error = new StringWriter();
        var leanReportDigest = RawLeanReportArtifact.ContentAddress(
            RawLeanReportArtifact.Write(truth.Snapshot, truth.Report).AsSpan());
        var provenance = new TruthGraphProvenance(
            SnapshotContentDigest.Compute(truth.Snapshot),
            leanReportDigest);
        DocumentGraphExportProjection documentProjection;
        try
        {
            documentProjection = DocumentGraphProjectionBuilder.AssembleRepository(
                repositoryRoot,
                DeclarationCatalog.Create(truth.Report),
                truth.Dag.Nodes.Select(static node => node.RepoPath.Value).ToHashSet(StringComparer.Ordinal));
        }
        catch (Exception exception) when (
            exception is InvalidOperationException
                or FormatException
                or IOException
                or UnauthorizedAccessException
                or ArgumentException)
        {
            return Failure("document graph could not be built", exception);
        }
        var exit = DagEmitter.Emit(
            repositoryRoot,
            truth.Dag,
            provenance,
            check,
            output,
            error,
            documentProjection);
        return new CommandResult(exit == 0, output.ToString(), error.ToString());
    }

    private static CommandResult Failure(string summary, Exception exception) =>
        new(false, string.Empty, $"dag-render: {summary}: {Innermost(exception).Message}\n");

    private static Exception Innermost(Exception exception) =>
        exception.InnerException is null ? exception : Innermost(exception.InnerException);
}
