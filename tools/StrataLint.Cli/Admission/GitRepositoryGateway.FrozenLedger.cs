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
        RequireTaggedObjectTypes(
            prefix,
            (references.CommitOids, "commit"),
            (references.TreeOids, "tree"),
            (references.BlobOids, "blob"));

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

        var trees = new Dictionary<string, ImmutableArray<GitRepositoryTreeEntry>>(StringComparer.Ordinal);
        foreach (var input in references.Inputs)
        {
            if (!RepoPath.TryCreate(input.DescriptorSelector, out var descriptorPath))
            {
                throw SemanticRejection(
                    "unsupported frozen Git descriptor selector");
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
                entries = GitRepositorySnapshotReader.ParseTree(
                    GitBytes("ls-tree", "-r", "-z", tree)).ToImmutableArray();
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

        return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
    }

    // Validate the existence and type of every referenced object in a single
    // `git cat-file --batch-check` invocation. The prior implementation spawned one
    // `git cat-file -t` process per object id; a frozen ledger with tens of thousands
    // of references then paid tens of thousands of sequential process spawns (minutes
    // of wall clock, growing with every freeze). Batching feeds all ids on stdin and
    // reads one strictly-parsed header line per id. The admission verdict is preserved:
    // a `<oid> missing` line is a MissingObject rejection (the object the old exit-128
    // path rejected), a type mismatch is a WrongObjectType rejection with the same
    // message, and any output that is not exactly a missing or `<oid> <type> <size>`
    // frame is rejected as an infrastructure error. One diagnostic detail changes: a
    // missing object arrives on a zero-exit `missing` line, so its rejection carries no
    // GitCommandFailure (parity with WrongObjectType, which never carried one); a real
    // git fault still exits non-zero and surfaces as GitInfrastructureException. No
    // caller reads the rejection's GitFailure — the sole catch site reads only Message.
    private void RequireTaggedObjectTypes(
        string repositoryPrefix,
        params (ImmutableArray<string> Oids, string Expected)[] groups)
    {
        var expectations = new List<(string ObjectId, string Expected, string Display)>();
        foreach (var (oids, expected) in groups)
        {
            foreach (var oid in oids)
            {
                if (!oid.StartsWith(repositoryPrefix, StringComparison.Ordinal))
                {
                    throw SemanticRejection(
                        $"frozen Git object {oid} does not use repository object format {repositoryPrefix[..^1]}");
                }

                expectations.Add((Untag(oid), expected, oid));
            }
        }

        if (expectations.Count == 0)
        {
            return;
        }

        var arguments = new[] { "cat-file", "--batch-check" };
        var standardInput = StrictUtf8.GetBytes(
            string.Concat(expectations.Select(static expectation => expectation.ObjectId + "\n")));
        var result = GitRaw(arguments, allowNonzero: false, standardInput: standardInput);

        string text;
        try
        {
            text = StrictUtf8.GetString(result.StandardOutput);
        }
        catch (System.Text.DecoderFallbackException exception)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.InvalidOutput,
                arguments,
                detail: exception.Message,
                exception: exception);
        }

        // `git cat-file --batch-check` emits exactly one newline-terminated line per input
        // id, in input order. Splitting on '\n' yields those lines plus a trailing empty
        // element after the final newline.
        var lines = text.Split('\n');
        if (lines.Length != expectations.Count + 1 || lines[^1].Length != 0)
        {
            throw InfrastructureFailure(
                GitCommandFailureKind.InvalidOutput,
                arguments,
                detail: "git cat-file --batch-check emitted an unexpected line count");
        }

        for (var index = 0; index < expectations.Count; index++)
        {
            var (objectId, expected, display) = expectations[index];
            // Split on single spaces without collapsing: git emits exactly one SP
            // between fields, so leading, trailing, or repeated spaces produce empty
            // fields that fail the field-count checks below rather than being tolerated.
            var fields = lines[index].Split(' ');
            if (fields.Length < 2 || !string.Equals(fields[0], objectId, StringComparison.Ordinal))
            {
                throw InfrastructureFailure(
                    GitCommandFailureKind.InvalidOutput,
                    arguments,
                    detail: $"git cat-file --batch-check emitted invalid data for object {objectId}");
            }

            if (string.Equals(fields[1], "missing", StringComparison.Ordinal))
            {
                // A missing frame is strictly `<oid> missing`; any extra token is malformed.
                if (fields.Length != 2)
                {
                    throw InfrastructureFailure(
                        GitCommandFailureKind.InvalidOutput,
                        arguments,
                        detail: $"git cat-file --batch-check emitted invalid data for object {objectId}");
                }

                throw new FrozenReferenceRejectionException(
                    FrozenReferenceRejectionKind.MissingObject,
                    $"frozen Git object {display} is not a reachable {expected}");
            }

            // A present frame is strictly `<oid> <type> <size>`, where size is a
            // non-negative decimal object size. Validating the size token keeps the
            // trust boundary fully fail-closed: any output that is not exactly this
            // shape is rejected as infrastructure error rather than silently accepted.
            if (fields.Length != 3
                || !long.TryParse(
                    fields[2],
                    System.Globalization.NumberStyles.None,
                    System.Globalization.CultureInfo.InvariantCulture,
                    out _))
            {
                throw InfrastructureFailure(
                    GitCommandFailureKind.InvalidOutput,
                    arguments,
                    detail: $"git cat-file --batch-check emitted invalid data for object {objectId}");
            }

            if (!string.Equals(fields[1], expected, StringComparison.Ordinal))
            {
                throw new FrozenReferenceRejectionException(
                    FrozenReferenceRejectionKind.WrongObjectType,
                    $"frozen Git object {display} has type {fields[1]}; expected {expected}");
            }
        }
    }

    private static FrozenReferenceRejectionException SemanticRejection(string message) =>
        new(FrozenReferenceRejectionKind.InvalidReference, message);

    private static string Untag(string oid) => oid[(oid.IndexOf(':') + 1)..];
}
