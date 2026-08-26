using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    private const string AlignOption = "--align-scribe-receipt";

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        DateTimeOffset recordedAtUtc,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        var alignOptionCount = arguments.Count(static argument => argument == AlignOption);
        if (alignOptionCount == 0)
        {
            return RunSingle(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                recordedAtUtc,
                arguments);
        }

        if (alignOptionCount != 1 || arguments[^1] != AlignOption)
        {
            return AlignedCoverFailure("align option must occur exactly once at the end");
        }

        var coverArguments = arguments.Take(arguments.Count - 1).ToArray();
        CoverArguments options;
        try
        {
            options = ParseArguments(coverArguments);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return AlignedCoverFailure(exception.Message);
        }

        var cachedReportSource = new SingleLoadLeanReportSource(leanReportSource);
        var cover = RunSingle(
            repositoryRoot,
            repository,
            cachedReportSource,
            scribeEmissionVerifier,
            recordedAtUtc,
            coverArguments);
        var resumed = !cover.Success && cover.Error.Contains(
            $"cover atom {options.AtomId} already has coverage:",
            StringComparison.Ordinal);
        if (!cover.Success && !resumed)
        {
            return cover with
            {
                Error = "COVER_ATOM_ALIGNED cover=failed\n" + cover.Error,
            };
        }

        var alignArguments = options.Gids
            .SelectMany(gid => new[] { "--atom-id", options.AtomId, "--gid", gid })
            .Concat(["--base", options.BaselineRevision])
            .ToArray();
        try
        {
            var aligned = AlignScribeReceipt(
                repositoryRoot,
                repository,
                cachedReportSource,
                scribeEmissionVerifier,
                alignArguments);
            var coverState = resumed ? "resumed" : "passed";
            return new CommandResult(
                true,
                $"COVER_ATOM_ALIGNED cover={coverState} align=passed\n"
                + (resumed ? cover.Error : cover.Output)
                + aligned.Output,
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            var coverState = resumed ? "resumed" : "passed";
            return new CommandResult(
                false,
                resumed ? cover.Error : cover.Output,
                $"COVER_ATOM_ALIGNED cover={coverState} align=failed\n"
                + $"ALIGN_SCRIBE_RECEIPT_INVALID {exception.Message}\n");
        }
    }

    private static CommandResult AlignedCoverFailure(string message) => new(
        false,
        string.Empty,
        $"COVER_ATOM_ALIGNED cover=failed\nCOVER_INVALID {message}\n");

    private sealed class SingleLoadLeanReportSource(ILeanReportSource source) : ILeanReportSource
    {
        private LeanAxiomReport? report;

        public LeanAxiomReport Load(RepositorySnapshot snapshot) =>
            report ??= source.Load(snapshot);
    }
}
