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
            throw new InvalidOperationException("frozen revision must be an exact commit OID");
        }

        var resolved = GitText("rev-parse", "--verify", $"{revision}^{{commit}}").Trim();
        if (!string.Equals(revision, resolved, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("frozen revision did not resolve byte-exactly");
        }

        var tree = GitText("rev-parse", "--verify", $"{resolved}^{{tree}}").Trim();
        var algorithm = resolved.Length == 40 ? "git-sha1:" : "git-sha256:";
        return new FrozenRevisionIdentity(resolved, algorithm + resolved, algorithm + tree);
    }
}
