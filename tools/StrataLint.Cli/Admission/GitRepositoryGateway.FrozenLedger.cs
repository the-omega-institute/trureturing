using System.Collections.Immutable;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class GitRepositoryGateway
{
    internal FrozenRevisionIdentity ResolveReference(string revision)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(revision);
        var resolved = GitText("rev-parse", "--verify", $"{revision}^{{commit}}").Trim();
        return ResolveFrozenRevision(resolved);
    }

    internal void RequireStrictAncestor(string ancestor, string descendant)
    {
        if (string.Equals(ancestor, descendant, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("C0 base must be a strict ancestor of the preimage");
        }

        var result = GitRaw(
            new[] { "merge-base", "--is-ancestor", ancestor, descendant },
            allowNonzero: true);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException("C0 base is not an ancestor of the preimage");
        }
    }

    internal ImmutableArray<string> WorkingTreeChanges() =>
        ParseNulStrings(GitBytes("diff", "--name-only", "-z", "HEAD", "--"))
            .Concat(ParseNulStrings(GitBytes("ls-files", "--others", "--exclude-standard", "-z")))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();

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
                "EnvironmentRecoordinate lean-toolchain pin");
            RequireTreeBlob(
                entries,
                reference.Environment.LakefilePath.Value,
                reference.Environment.LakefileBlobOid,
                "EnvironmentRecoordinate lakefile pin");
            RequireTreeBlob(
                entries,
                "lake-manifest.json",
                reference.Environment.LakeManifestBlobOid,
                "EnvironmentRecoordinate lake-manifest pin");
            var sourceBytes = GitBytes("cat-file", "blob", Untag(reference.Input.DescriptorBlobOid));
            var sourceSha256 = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(sourceBytes));
            if (!string.Equals(sourceSha256, reference.SourceSha256, StringComparison.Ordinal))
            {
                throw SemanticRejection(
                    "EnvironmentRecoordinate source_sha256 does not match descriptor blob bytes");
            }
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
