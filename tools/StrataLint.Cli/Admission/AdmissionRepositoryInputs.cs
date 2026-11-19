using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class AdmissionRepositoryInputs
{
    internal static RawRepositorySnapshot ReadCurrent(IRepositoryGateway repository) =>
        repository.ReadCurrentProjection(NeedsBody);

    internal static RawRepositorySnapshot ReadBaseline(IRepositoryGateway repository, string revision) =>
        repository.ReadRevisionProjection(revision, NeedsBody);

    private static bool NeedsBody(string path) =>
        !HistoricalTheoryPaths.IsAuxiliaryData(RepoPath.CreateKnown(path));
}
