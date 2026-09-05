using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.Scribe.Documents;
using Trureturing.Truth;

namespace StrataLint.Cli;

/// Projects the repository truth graph to Generated/DAG.md.
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
        TruthDagProjection projection;
        try
        {
            projection = TruthDagProjectionAssembler.Build(truth.Snapshot, truth.Lean);
        }
        catch (InvalidOperationException exception)
        {
            return Failure("truth projection could not be built", exception);
        }
        var leanReportDigest = RawLeanReportArtifact.ContentAddress(
            RawLeanReportArtifact.Write(truth.Snapshot, truth.Report).AsSpan());
        DocumentGraphExportProjection documentProjection;
        try
        {
            documentProjection = DocumentGraphExportProjectionExtensions.AssembleRepository(
                DocumentAssembly.Value,
                repositoryRoot,
                DeclarationCatalog.Create(truth.Report),
                projection.Nodes.Select(static node => node.RepoPath.Value).ToHashSet(StringComparer.Ordinal));
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
        var provenance = new TruthGraphProvenance(
            SnapshotContentDigest.Compute(
                truth.Snapshot,
                documentProjection.Documents.Nodes.Select(static node => node.RepoPath)),
            leanReportDigest);
        var exit = DagEmitter.Emit(
            repositoryRoot,
            projection,
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
