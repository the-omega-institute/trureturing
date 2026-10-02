using System.Reflection;
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
        string? packPath = null;
        string? packDigest = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            var argument = arguments[index];
            if (argument == "--check")
            {
                check = true;
                continue;
            }

            if (argument is "--scribe-pack" or "--scribe-pack-digest")
            {
                if (++index == arguments.Count)
                    return Usage($"{argument} requires a value");
                var value = arguments[index];
                if (argument == "--scribe-pack" && packPath is null)
                    packPath = value;
                else if (argument == "--scribe-pack-digest" && packDigest is null)
                    packDigest = value;
                else
                    return Usage($"duplicate argument {argument}");
                continue;
            }

            return Usage($"unknown argument {argument}");
        }

        if ((packPath is null) != (packDigest is null))
            return Usage("--scribe-pack and --scribe-pack-digest must be supplied together");
        if (packDigest is not null && !ScribePackInput.IsDigest(packDigest))
            return Usage("scribe pack digest must contain exactly 64 hexadecimal characters");
        if (packPath is not null && string.IsNullOrWhiteSpace(packPath))
            return Usage("--scribe-pack requires a nonempty path");

        IEnumerable<DocumentDefinition>? definitions = null;
        if (packPath is not null)
        {
            try
            {
                definitions = ScribePackInput.ReadDefinitions(packPath, packDigest!);
            }
            catch (FormatException exception)
            {
                return new CommandResult(false, string.Empty, $"dag-render: {exception.Message}\n");
            }
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

        return definitions is null
            ? Run(repositoryRoot, truth, check, typeof(DocumentAssembly).Assembly)
            : Run(repositoryRoot, truth, check, definitions);
    }

    internal static CommandResult Run(
        string repositoryRoot,
        TruthContext truth,
        bool check,
        Assembly documentsAssembly) => RunCore(repositoryRoot, truth, check,
            () => DocumentDefinitions.Discover(documentsAssembly, repositoryRoot));

    internal static CommandResult Run(
        string repositoryRoot,
        TruthContext truth,
        bool check,
        IEnumerable<DocumentDefinition> definitions) => RunCore(repositoryRoot, truth, check, () => definitions);

    private static CommandResult RunCore(
        string repositoryRoot,
        TruthContext truth,
        bool check,
        Func<IEnumerable<DocumentDefinition>> definitions)
    {
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
                definitions(),
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

    private static CommandResult Usage(string message) => new(false, string.Empty,
        $"dag-render: {message}\nusage: dag-render [--check] [--scribe-pack FILE --scribe-pack-digest HEX64]\n");

    private static Exception Innermost(Exception exception) =>
        exception.InnerException is null ? exception : Innermost(exception.InnerException);
}
