using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class ConservativeReplayWorkspace : IDisposable
{
    private readonly string temporaryRoot;
    private bool disposed;

    private ConservativeReplayWorkspace(
        string temporaryRoot,
        string baselineRoot,
        string candidateRoot,
        string baselineLeanReport,
        string candidateLeanReport)
    {
        this.temporaryRoot = temporaryRoot;
        BaselineRoot = baselineRoot;
        CandidateRoot = candidateRoot;
        BaselineLeanReport = baselineLeanReport;
        CandidateLeanReport = candidateLeanReport;
    }

    internal string BaselineRoot { get; }

    internal string CandidateRoot { get; }

    internal string BaselineLeanReport { get; }

    internal string CandidateLeanReport { get; }

    internal static ConservativeReplayWorkspace Materialize(ConservativeReplayEnvelope replay)
    {
        ArgumentNullException.ThrowIfNull(replay);
        var temporary = Path.Combine(
            Path.GetTempPath(),
            "stratalint-conservative-replay-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(temporary);
        try
        {
            var bundle = Path.Combine(temporary, "repository.bundle");
            var reports = Path.Combine(temporary, "reports");
            var baselineReport = Path.Combine(reports, "baseline.json");
            var candidateReport = Path.Combine(reports, "candidate.json");
            Directory.CreateDirectory(reports);
            File.WriteAllBytes(bundle, replay.RepositoryBundle.AsSpan());
            File.WriteAllBytes(baselineReport, replay.BaselineLeanReport.AsSpan());
            File.WriteAllBytes(candidateReport, replay.CandidateLeanReport.AsSpan());
            var baselineRoot = Path.Combine(temporary, "baseline");
            var candidateRoot = Path.Combine(temporary, "candidate");
            Restore(bundle, baselineRoot, replay.BaselineIdentity);
            Restore(bundle, candidateRoot, replay.CandidateIdentity);
            return new ConservativeReplayWorkspace(
                temporary,
                baselineRoot,
                candidateRoot,
                baselineReport,
                candidateReport);
        }
        catch
        {
            Directory.Delete(temporary, recursive: true);
            throw;
        }
    }

    public void Dispose()
    {
        if (disposed) return;
        disposed = true;
        Directory.Delete(temporaryRoot, recursive: true);
    }

    private static void Restore(
        string bundle,
        string root,
        ConservativeRepositoryIdentity expected)
    {
        Git(Path.GetDirectoryName(bundle)!, ["clone", "--no-checkout", "--quiet", bundle, root]);
        Git(root, ["checkout", "--detach", "--quiet", expected.CommitOid]);
        var actual = new GitRepositoryGateway(root).ResolveCurrentRevision();
        if (actual.Revision != expected.CommitOid || actual.TreeOid != expected.TreeOid)
        {
            throw new InvalidOperationException(
                "replay bundle checkout does not match its frozen repository identity");
        }

        var status = Git(root, ["status", "--porcelain", "--untracked-files=all"]);
        if (status.StandardOutput.Length != 0)
        {
            throw new InvalidOperationException("replay bundle checkout is not clean");
        }
    }

    private static ProcessOutput Git(string root, IEnumerable<string> arguments)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            arguments,
            root,
            TimeSpan.FromMinutes(2),
            8 * 1024 * 1024);
        if (result.ExitCode != 0 || result.StandardError.Length != 0)
        {
            throw new InvalidOperationException(
                Encoding.UTF8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                    ? error
                    : $"git replay command exited {result.ExitCode}");
        }

        return result;
    }
}
