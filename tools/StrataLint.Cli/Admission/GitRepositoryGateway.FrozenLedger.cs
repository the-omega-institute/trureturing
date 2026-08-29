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
