using System.Collections.Immutable;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class GitRepositoryGateway
{
    public RawRepositorySnapshot ReadEnvironmentPinBlobs(FrozenLedgerInput input)
    {
        ArgumentNullException.ThrowIfNull(input);
        var supporting = input.SupportingBlobOids;
        if (supporting.Length != 2 || supporting.Distinct(StringComparer.Ordinal).Count() != 2)
        {
            throw new InvalidOperationException(
                "protected semantic pins require exactly two distinct supporting blob OIDs");
        }

        if (!FrozenHashSyntax.IsGitOid(input.BaseTreeOid)
            || supporting.Any(static oid => !FrozenHashSyntax.IsGitOid(oid)))
        {
            throw new InvalidOperationException(
                "protected semantic pin input contains a malformed Git OID");
        }

        var prefix = input.BaseTreeOid.StartsWith("git-sha1:", StringComparison.Ordinal)
            ? "git-sha1:"
            : "git-sha256:";
        if (supporting.Any(oid => !oid.StartsWith(prefix, StringComparison.Ordinal)))
        {
            throw new InvalidOperationException(
                "protected semantic pin input mixes Git object hash algorithms");
        }

        var tree = ParseTree(GitBytes(
                "ls-tree",
                "-l",
                "-z",
                Untag(input.BaseTreeOid),
                "--",
                "lake-manifest.json",
                "lean-toolchain"))
            .ToArray();
        var expectedPaths = new HashSet<string>(StringComparer.Ordinal)
        {
            "lake-manifest.json",
            "lean-toolchain",
        };
        var treeOids = tree
            .Where(entry => expectedPaths.Contains(entry.Path)
                && entry.Mode is "100644" or "100755"
                && entry.ObjectType == "blob")
            .Select(entry => prefix + entry.ObjectId)
            .ToHashSet(StringComparer.Ordinal);
        if (tree.Length != 2
            || treeOids.Count != 2
            || !treeOids.SetEquals(supporting))
        {
            throw new InvalidOperationException(
                "protected supporting blob OIDs do not resolve to lean-toolchain and lake-manifest.json");
        }

        return RawRepositorySnapshot.Create(ReadTreeBlobs(
            tree,
            entry => $"protected semantic pin has non-regular entry {entry.Path} ({entry.Mode} {entry.ObjectType})"));
    }

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

    public TrustedFrozenGitReferences ValidateFrozenReferences(FrozenLedgerReferenceSet references)
    {
        ArgumentNullException.ThrowIfNull(references);
        var objectFormat = GitText("rev-parse", "--show-object-format").Trim();
        var prefix = objectFormat switch
        {
            "sha1" => "git-sha1:",
            "sha256" => "git-sha256:",
            _ => throw InfrastructureFailure(
                GitCommandFailureKind.InvalidOutput,
                ["rev-parse", "--show-object-format"],
                detail: $"unsupported Git object format {objectFormat}"),
        };
        foreach (var oid in references.CommitOids)
        {
            RequireTaggedObjectType(oid, prefix, "commit");
        }

        foreach (var oid in references.TreeOids)
        {
            RequireTaggedObjectType(oid, prefix, "tree");
        }

        foreach (var oid in references.BlobOids)
        {
            RequireTaggedObjectType(oid, prefix, "blob");
        }

        if (!references.RequiredAncestorCommitOids.IsEmpty)
        {
            var candidateHead = GitText("rev-parse", "--verify", "HEAD^{commit}").Trim();
            foreach (var oid in references.RequiredAncestorCommitOids)
            {
                var arguments = new[]
                {
                    "merge-base", "--is-ancestor", Untag(oid), candidateHead,
                };
                var result = GitRaw(arguments, allowNonzero: true);
                if (result.ExitCode == 1)
                {
                    throw SemanticRejection(
                        $"frozen base_commit_oid {oid} is not an ancestor of candidate HEAD");
                }

                if (result.ExitCode != 0)
                {
                    throw InfrastructureFailure(
                        GitCommandFailureKind.NonzeroExit,
                        arguments,
                        exitCode: result.ExitCode,
                        standardError: DecodeFailureText(result.StandardError));
                }
            }
        }

        var trees = new Dictionary<string, ImmutableArray<TreeEntry>>(StringComparer.Ordinal);
        foreach (var input in references.Inputs)
        {
            if (input.Materializer != "repository-snapshot-v1"
                || !RepoPath.TryCreate(input.DescriptorSelector, out var descriptorPath))
            {
                throw SemanticRejection(
                    "unsupported frozen Git materializer or descriptor selector");
            }

            var inputPrefix = input.BaseCommitOid.StartsWith("git-sha1:", StringComparison.Ordinal)
                ? "git-sha1:"
                : "git-sha256:";
            var allOids = new[]
            {
                input.BaseCommitOid,
                input.BaseTreeOid,
                input.DescriptorBlobOid,
            }.Concat(input.SupportingBlobOids).ToArray();
            if (allOids.Any(oid => !oid.StartsWith(inputPrefix, StringComparison.Ordinal)))
            {
                throw SemanticRejection("frozen Git references mix object hash algorithms");
            }

            var commit = Untag(input.BaseCommitOid);
            var tree = Untag(input.BaseTreeOid);
            var commitTree = GitText("rev-parse", "--verify", $"{commit}^{{tree}}").Trim();
            if (commitTree != tree)
            {
                throw SemanticRejection(
                    "frozen base_commit_oid does not resolve to base_tree_oid");
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
                throw SemanticRejection(
                    "frozen descriptor selector does not resolve to descriptor_blob_oid in base_tree_oid");
            }

            var treeBlobIds = entries
                .Where(static entry => entry.ObjectType == "blob")
                .Select(static entry => entry.ObjectId)
                .ToHashSet(StringComparer.Ordinal);
            if (input.SupportingBlobOids.Any(oid => !treeBlobIds.Contains(Untag(oid))))
            {
                throw SemanticRejection(
                    "frozen supporting blob is not reachable from base_tree_oid");
            }
        }

        foreach (var reference in references.EnvironmentReferences)
        {
            var tree = Untag(reference.Input.BaseTreeOid);
            if (!trees.TryGetValue(tree, out var entries))
            {
                entries = ParseTree(GitBytes("ls-tree", "-r", "-z", tree)).ToImmutableArray();
                trees.Add(tree, entries);
            }

            RequireTreeBlob(
                entries,
                "lean-toolchain",
                reference.Environment.LeanToolchainBlobOid,
                "Supersede lean-toolchain pin");
            RequireTreeBlob(
                entries,
                reference.Environment.LakefilePath.Value,
                reference.Environment.LakefileBlobOid,
                "Supersede lakefile pin");
            RequireTreeBlob(
                entries,
                "lake-manifest.json",
                reference.Environment.LakeManifestBlobOid,
                "Supersede lake-manifest pin");
        }

        return TrustedFrozenGitReferences.CreateForTrustedAdapter(
            references.Inputs,
            references.EnvironmentReferences);
    }

    private static void RequireTreeBlob(
        ImmutableArray<TreeEntry> entries,
        string path,
        string taggedOid,
        string label)
    {
        var entry = entries.SingleOrDefault(item => item.Path == path);
        if (entry is null
            || entry.ObjectType != "blob"
            || entry.Mode is not ("100644" or "100755")
            || entry.ObjectId != Untag(taggedOid))
        {
            throw SemanticRejection($"{label} does not resolve to its named path");
        }
    }

    private void RequireTaggedObjectType(string oid, string repositoryPrefix, string expected)
    {
        if (!oid.StartsWith(repositoryPrefix, StringComparison.Ordinal))
        {
            throw SemanticRejection(
                $"frozen Git object {oid} does not use repository object format {repositoryPrefix[..^1]}");
        }

        RequireObjectType(Untag(oid), expected, oid);
    }

    private void RequireObjectType(string objectId, string expected, string? display = null)
    {
        var arguments = new[] { "cat-file", "-t", objectId };
        var result = GitRaw(arguments, allowNonzero: true);
        if (result.ExitCode != 0)
        {
            var infrastructure = InfrastructureFailure(
                GitCommandFailureKind.NonzeroExit,
                arguments,
                exitCode: result.ExitCode,
                standardError: DecodeFailureText(result.StandardError));
            if (result.ExitCode == 128)
            {
                throw new FrozenReferenceRejectionException(
                    FrozenReferenceRejectionKind.MissingObject,
                    $"frozen Git object {display ?? objectId} is not a reachable {expected}",
                    infrastructure.Failure);
            }

            throw infrastructure;
        }

        string actual;
        try
        {
            actual = StrictUtf8.GetString(result.StandardOutput).Trim();
        }
        catch (System.Text.DecoderFallbackException exception)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.InvalidOutput,
                arguments,
                detail: exception.Message,
                exception: exception);
        }

        if (actual != expected)
        {
            throw new FrozenReferenceRejectionException(
                FrozenReferenceRejectionKind.WrongObjectType,
                $"frozen Git object {display ?? objectId} has type {actual}; expected {expected}");
        }
    }

    private static FrozenReferenceRejectionException SemanticRejection(string message) =>
        new(FrozenReferenceRejectionKind.InvalidReference, message);

    private static string Untag(string oid) => oid[(oid.IndexOf(':') + 1)..];
}
