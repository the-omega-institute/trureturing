using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class GitRepositoryGateway
{
    public FrozenRevisionIdentity ResolveCurrentRevision()
    {
        var revision = GitText("rev-parse", "--verify", "HEAD^{commit}").Trim();
        return ResolveFrozenRevision(revision);
    }

    public FrozenRevisionIdentity ResolveFrozenRevision(string revision)
    {
        if (!IsObjectId(revision))
        {
            throw new InvalidOperationException("ledger genesis revision must be an exact commit OID");
        }

        var resolved = GitText("rev-parse", "--verify", $"{revision}^{{commit}}").Trim();
        if (!string.Equals(revision, resolved, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("ledger genesis revision did not resolve byte-exactly");
        }

        var tree = GitText("rev-parse", "--verify", $"{resolved}^{{tree}}").Trim();
        var algorithm = resolved.Length == 40 ? "git-sha1:" : "git-sha256:";
        return new FrozenRevisionIdentity(resolved, algorithm + resolved, algorithm + tree);
    }

    public RawRepositorySnapshot ReadFrozenRevision(string revision)
    {
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        foreach (var entry in ParseTree(GitBytes("ls-tree", "-r", "-z", revision)))
        {
            if (entry.Mode is not ("100644" or "100755" or "120000") || entry.ObjectType != "blob")
            {
                throw new InvalidOperationException(
                    $"frozen revision has unsupported entry {entry.Path} ({entry.Mode} {entry.ObjectType})");
            }

            var bytes = GitBytes("show", $"{revision}:{entry.Path}");
            entries.Add(new RawRepositoryEntry(entry.Path, ImmutableArray.CreateRange(bytes)));
        }

        return RawRepositorySnapshot.Create(entries);
    }

    public TrustedFrozenGitReferences ValidateFrozenReferences(FrozenLedgerReferenceSet references)
    {
        ArgumentNullException.ThrowIfNull(references);
        var trees = new Dictionary<string, ImmutableArray<TreeEntry>>(StringComparer.Ordinal);
        foreach (var input in references.Inputs)
        {
            if (input.Materializer != "repository-snapshot-v1"
                || !RepoPath.TryCreate(input.DescriptorSelector, out var descriptorPath))
            {
                throw new InvalidOperationException("unsupported frozen Git materializer or descriptor selector");
            }

            var prefix = input.BaseCommitOid.StartsWith("git-sha1:", StringComparison.Ordinal)
                ? "git-sha1:"
                : "git-sha256:";
            var allOids = new[]
            {
                input.BaseCommitOid,
                input.BaseTreeOid,
                input.DescriptorBlobOid,
            }.Concat(input.SupportingBlobOids).ToArray();
            if (allOids.Any(oid => !oid.StartsWith(prefix, StringComparison.Ordinal)))
            {
                throw new InvalidOperationException("frozen Git references mix object hash algorithms");
            }

            var commit = Untag(input.BaseCommitOid);
            var tree = Untag(input.BaseTreeOid);
            RequireObjectType(commit, "commit");
            RequireObjectType(tree, "tree");
            RequireObjectType(Untag(input.DescriptorBlobOid), "blob");
            foreach (var supporting in input.SupportingBlobOids)
            {
                RequireObjectType(Untag(supporting), "blob");
            }

            var commitTree = GitText("rev-parse", "--verify", $"{commit}^{{tree}}").Trim();
            if (commitTree != tree)
            {
                throw new InvalidOperationException("frozen base_commit_oid does not resolve to base_tree_oid");
            }

            if (!trees.TryGetValue(tree, out var entries))
            {
                entries = ParseTree(GitBytes("ls-tree", "-r", "-z", tree)).ToImmutableArray();
                trees.Add(tree, entries);
            }

            var descriptor = entries.SingleOrDefault(entry => entry.Path == descriptorPath.Value);
            if (descriptor is null
                || descriptor.ObjectType != "blob"
                || descriptor.Mode is not ("100644" or "100755")
                || descriptor.ObjectId != Untag(input.DescriptorBlobOid))
            {
                throw new InvalidOperationException(
                    "frozen descriptor selector does not resolve to descriptor_blob_oid in base_tree_oid");
            }

            var treeBlobIds = entries
                .Where(static entry => entry.ObjectType == "blob")
                .Select(static entry => entry.ObjectId)
                .ToHashSet(StringComparer.Ordinal);
            if (input.SupportingBlobOids.Any(oid => !treeBlobIds.Contains(Untag(oid))))
            {
                throw new InvalidOperationException("frozen supporting blob is not reachable from base_tree_oid");
            }
        }

        return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
    }

    private void RequireObjectType(string objectId, string expected)
    {
        var result = GitRaw(new[] { "cat-file", "-t", objectId }, allowNonzero: true);
        var actual = result.ExitCode == 0
            ? StrictUtf8.GetString(result.StandardOutput).Trim()
            : string.Empty;
        if (actual != expected)
        {
            throw new InvalidOperationException($"frozen Git object {objectId} is not a reachable {expected}");
        }
    }

    private static string Untag(string oid) => oid[(oid.IndexOf(':') + 1)..];
}
