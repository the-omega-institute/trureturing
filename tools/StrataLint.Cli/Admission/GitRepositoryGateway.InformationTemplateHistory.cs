using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class GitRepositoryGateway : IInformationTemplateHistoryRepository
{
    string IInformationTemplateHistoryRepository.CurrentRevision => ResolveCurrentRevision().Revision;

    string IInformationTemplateHistoryRepository.ResolveBase(string? requested)
    {
        var head = ResolveCurrentRevision().Revision;
        var revision = requested is null ? head : GitText("rev-parse", "--verify", "--end-of-options", requested + "^{commit}").Trim();
        InformationTemplateJson.Hash(revision, 40);
        if (GitRaw(["merge-base", "--is-ancestor", revision, head], allowNonzero: true).ExitCode != 0)
            throw new InvalidOperationException("history protected base must be an ancestor of HEAD");
        return revision;
    }

    RawRepositorySnapshot IInformationTemplateHistoryRepository.ReadPredicate(string? revision)
    {
        static bool Include(string path) => path.StartsWith(InformationTemplateDebtStore.Root, StringComparison.Ordinal);
        static bool Bytes(string path) => path == InformationTemplateDebtStore.ActivationPath;
        return revision is null ? GitRepositorySnapshotReader.ReadCurrent(root, Include, Bytes)
            : GitRepositorySnapshotReader.ReadRevision(revision,
                (args, maximum, input) => GitRaw(args, false, maximum, input), Include, Bytes);
    }

    RawRepositorySnapshot IInformationTemplateHistoryRepository.ReadCandidate() => ReadCurrent();
    RawRepositorySnapshot IInformationTemplateHistoryRepository.ReadHistorical(string revision)
    {
        ResolveFrozenRevision(InformationTemplateJson.Hash(revision, 40));
        return ReadRevision(revision);
    }
}
