using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAppendWriter
{
    internal static CommandResult Append(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments) =>
        DagLedgerAlignWriter.AppendAlias(repositoryRoot, repository, arguments);

    internal static ImmutableArray<RepositoryFile> BuildNewEventFiles(
        IEnumerable<FrozenLedgerDraft> drafts)
    {
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        foreach (var draft in drafts)
        {
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                draft.EventType,
                draft.Payload);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(encoded.Hash);
            var path = RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json");
            files.Add(new RepositoryFile(
                path,
                encoded.Bytes,
                Encoding.UTF8.GetString(encoded.Bytes.AsSpan())));
        }

        return files.ToImmutable();
    }

    internal static string RenderFailure(string marker, Exception exception)
    {
        var detail = exception.InnerException is null
            ? exception.Message
            : exception.Message + " Cause: " + exception.InnerException.Message;
        return marker + " " + detail + "\n";
    }

}
