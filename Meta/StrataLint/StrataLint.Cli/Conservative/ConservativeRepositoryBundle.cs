using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ConservativeRepositoryBundle
{
    internal static byte[] Create(
        string baselineRoot,
        string candidateRoot,
        ConservativeRepositoryIdentity baselineIdentity,
        ConservativeRepositoryIdentity candidateIdentity,
        IEnumerable<string> evidenceCommitOids)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(baselineRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(candidateRoot);
        ArgumentNullException.ThrowIfNull(baselineIdentity);
        ArgumentNullException.ThrowIfNull(candidateIdentity);
        ArgumentNullException.ThrowIfNull(evidenceCommitOids);
        var evidence = evidenceCommitOids
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        RequireExactCommitOid(baselineIdentity.CommitOid);
        RequireExactCommitOid(candidateIdentity.CommitOid);
        foreach (var oid in evidence) RequireExactCommitOid(oid);
        var oidLengths = evidence
            .Append(baselineIdentity.CommitOid)
            .Append(candidateIdentity.CommitOid)
            .Select(static oid => oid.Length)
            .Distinct()
            .ToArray();
        if (oidLengths.Length != 1)
        {
            throw new InvalidOperationException("conservative bundle cannot mix Git object formats");
        }

        var temporary = Path.Combine(
            Path.GetTempPath(),
            "stratalint-conservative-bundle-" + Guid.NewGuid().ToString("N"));
        var repository = Path.Combine(temporary, "repository.git");
        var bundle = Path.Combine(temporary, "repository.bundle");
        Directory.CreateDirectory(temporary);
        try
        {
            var init = oidLengths[0] == 64
                ? new[] { "init", "--bare", "--quiet", "--object-format=sha256", repository }
                : ["init", "--bare", "--quiet", repository];
            RequireSuccess(Git(temporary, init), "git init failed");
            ImportExactCommit(repository, candidateIdentity.CommitOid, candidateRoot);
            ImportExactCommit(repository, baselineIdentity.CommitOid, baselineRoot, candidateRoot);
            for (var index = 0; index < evidence.Length; index++)
            {
                ImportExactCommit(repository, evidence[index], baselineRoot, candidateRoot);
                RequireSuccess(
                    Git(repository,
                    ["update-ref", $"refs/stratalint/evidence/{index:D6}", evidence[index]]),
                    "git evidence ref creation failed");
            }

            RequireSuccess(
                Git(repository, ["update-ref", "refs/heads/candidate", candidateIdentity.CommitOid]),
                "git candidate ref creation failed");
            RequireSuccess(
                Git(repository, ["update-ref", "refs/stratalint/baseline", baselineIdentity.CommitOid]),
                "git baseline ref creation failed");
            RequireSuccess(
                Git(repository, ["symbolic-ref", "HEAD", "refs/heads/candidate"]),
                "git HEAD creation failed");

            var revisions = new List<string>
            {
                "bundle", "create", bundle, "HEAD", "refs/stratalint/baseline",
            };
            revisions.AddRange(Enumerable.Range(0, evidence.Length)
                .Select(static index => $"refs/stratalint/evidence/{index:D6}"));
            RequireSuccess(Git(repository, revisions), "git bundle creation failed");
            return File.ReadAllBytes(bundle);
        }
        finally
        {
            Directory.Delete(temporary, recursive: true);
        }
    }

    private static void ImportExactCommit(string repository, string oid, params string[] sources)
    {
        ProcessOutput? last = null;
        foreach (var source in sources.Distinct(StringComparer.Ordinal))
        {
            last = Git(repository, ["fetch", "--no-tags", "--quiet", source, oid]);
            if (last.ExitCode != 0) continue;
            var type = Git(repository, ["cat-file", "-t", oid]);
            if (type.ExitCode == 0
                && string.Equals(
                    Encoding.UTF8.GetString(type.StandardOutput).Trim(),
                    "commit",
                    StringComparison.Ordinal))
            {
                return;
            }
        }

        throw Failure(last, $"exact frozen evidence commit is unavailable: {oid}");
    }

    private static void RequireExactCommitOid(string oid)
    {
        if (oid.Length is not (40 or 64) || oid.Any(static character => !char.IsAsciiHexDigit(character)))
        {
            throw new InvalidOperationException("conservative bundle requires exact commit OIDs");
        }
    }

    private static void RequireSuccess(ProcessOutput result, string fallback)
    {
        if (result.ExitCode != 0) throw Failure(result, fallback);
    }

    private static InvalidOperationException Failure(ProcessOutput? result, string fallback) =>
        new(result is not null
            && Encoding.UTF8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                ? error
                : fallback);

    private static ProcessOutput Git(string root, IEnumerable<string> arguments) =>
        BoundedProcessRunner.Run(
            "git",
            arguments,
            root,
            TimeSpan.FromMinutes(2),
            8 * 1024 * 1024);
}
