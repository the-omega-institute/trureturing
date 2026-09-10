using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Globalization;

namespace StrataLint.EngineeringScope;

internal sealed record TransportMaterial(string Path, string Sha256, int Mode);
internal sealed record CiTransportRecord(int Version, string Stage, string Candidate, string Round,
    string Commit, long RunId, int RunAttempt, string Repository, TransportMaterial[] Materials);

// The stage owns the file list and seals; this owner binds their transport to an
// exact upstream execution. Consumers bootstrap the transported runtime, then
// validate before invoking any current/delta or release command. Engineering's
// transport joins the shared build already present at its consumer. No rebuild occurs.
internal static class CiTransport
{
    internal static string ManifestPath(string stage) => CommonExecutionEvidence.RootPath + "/" + stage + "-transport.json";

    internal static string ArtifactName(string stage, long run, int attempt) => $"ci-{stage}-{run}-{attempt}";

    internal static int Run(IReadOnlyList<string> arguments, TextWriter output)
    {
        var values = new Dictionary<string, string>(StringComparer.Ordinal);
        for (var i = 1; i < arguments.Count; i += 2)
        {
            if (i + 1 == arguments.Count || !values.TryAdd(arguments[i], arguments[i + 1]))
                throw new ArgumentException("transport options must be unique name/value pairs");
        }
        var pack = arguments[0] == "transport-pack";
        var required = new[] { "--repository", "--stage", "--commit", "--run-id", "--run-attempt" }
            .Concat(pack ? ["--archive"] : []).Order(StringComparer.Ordinal);
        if (!required.SequenceEqual(values.Keys.Order(StringComparer.Ordinal)))
            throw new ArgumentException("transport-pack|transport-verify --repository ROOT --stage build|engineering|current --commit SHA --run-id ID --run-attempt N [--archive FILE]");
        var root = Path.GetFullPath(values["--repository"]);
        var stage = values["--stage"];
        var commit = values["--commit"];
        if (stage is not ("build" or "engineering" or "current") || commit.Length != 40 || !commit.All(char.IsAsciiHexDigit)
            || !long.TryParse(values["--run-id"], NumberStyles.None, CultureInfo.InvariantCulture, out var run) || run < 1
            || !int.TryParse(values["--run-attempt"], NumberStyles.None, CultureInfo.InvariantCulture, out var attempt) || attempt < 1)
            throw new ArgumentException("invalid transport stage or immutable execution identity");
        var repository = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "";
        if (Git(root, "rev-parse", "HEAD") != commit || Git(root, "status", "--porcelain", "--untracked-files=all").Length != 0)
            throw new InvalidDataException("transport requires the exact clean candidate commit");
        var common = stage switch
        {
            "build" => CommonExecutionEvidence.ValidateBuild(root),
            "current" => CommonExecutionEvidence.ValidateCurrent(root),
            _ => CommonExecutionEvidence.ValidateEngineering(root),
        };
        var manifestPath = ManifestPath(stage);
        if (pack)
        {
            var paths = ListedFiles(root, stage).Where(path => path != manifestPath).ToArray();
            CommonExecutionEvidence.Write(root, manifestPath, new CiTransportRecord(1, stage, common.Candidate, common.Round,
                commit, run, attempt, repository, paths.Select(path => new TransportMaterial(path,
                    CommonExecutionEvidence.Hash(Path.Combine(root, path)), Mode(Path.Combine(root, path)))).ToArray()));
            var archive = Path.GetFullPath(values["--archive"]);
            if (archive.StartsWith(Path.Combine(root, CommonExecutionEvidence.RootPath) + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                throw new ArgumentException("archive must be outside the stage evidence directory");
            Directory.CreateDirectory(Path.GetDirectoryName(archive)!);
            using (var file = File.Create(archive + ".tmp"))
            using (var gzip = new GZipStream(file, CompressionLevel.Fastest))
            using (var tar = new TarWriter(gzip))
                foreach (var path in paths.Append(manifestPath)) tar.WriteEntry(Path.Combine(root, path), path);
            File.Move(archive + ".tmp", archive, overwrite: true);
            var outputs = new Dictionary<string, string>
            {
                ["artifact_name"] = ArtifactName(stage, run, attempt), ["archive"] = archive,
                ["run_id"] = run.ToString(CultureInfo.InvariantCulture), ["run_attempt"] = attempt.ToString(CultureInfo.InvariantCulture),
                ["commit"] = commit, ["candidate"] = common.Candidate, ["round"] = common.Round,
            };
            if (Environment.GetEnvironmentVariable("GITHUB_OUTPUT") is { Length: > 0 } destination)
                File.AppendAllLines(destination, outputs.Select(pair => pair.Key + "=" + pair.Value));
        }
        else
        {
            var record = CommonExecutionEvidence.Read<CiTransportRecord>(root, manifestPath);
            if (record.Version != 1 || record.Stage != stage || record.Candidate != common.Candidate || record.Round != common.Round
                || record.Commit != commit || record.RunId != run || record.RunAttempt != attempt || record.Repository != repository)
                throw new InvalidDataException("transport candidate, stage, or upstream execution mismatch");
            if (!ListedFiles(root, stage).Where(path => path != manifestPath).SequenceEqual(record.Materials.Select(material => material.Path)))
                throw new InvalidDataException("transport does not contain the complete stage file list");
            foreach (var material in record.Materials)
                if (CommonExecutionEvidence.Hash(Path.Combine(root, material.Path)) != material.Sha256 || Mode(Path.Combine(root, material.Path)) != material.Mode)
                    throw new InvalidDataException("transport hash or mode mismatch: " + material.Path);
        }
        output.WriteLine($"CI_TRANSPORT stage={stage} candidate={common.Candidate} round={common.Round} commit={commit} run_id={run} run_attempt={attempt} status={(pack ? "packed" : "verified")}");
        return 0;
    }

    private static string[] ListedFiles(string root, string stage)
    {
        var text = File.ReadAllText(Path.Combine(root, CommonExecutionEvidence.BundleListPath(stage)));
        if (!text.EndsWith('\0')) throw new InvalidDataException("stage transport list is not NUL terminated");
        var summary = CommonExecutionEvidence.RootPath + "/" + stage + "-result.json";
        return text.Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Concat(File.Exists(Path.Combine(root, summary)) ? [summary] : []).SelectMany(path =>
        {
            if (Path.IsPathRooted(path) || path.Split('/').Any(part => part is ".." or "." or ""))
                throw new InvalidDataException("invalid stage artifact path");
            var full = Path.Combine(root, path);
            return Directory.Exists(full) ? Directory.GetFiles(full, "*", SearchOption.AllDirectories)
                .Select(file => Path.GetRelativePath(root, file).Replace('\\', '/')) : [path];
        }).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
    }

    private static int Mode(string path) => OperatingSystem.IsWindows() ? 0 : (int)File.GetUnixFileMode(path);

    private static string Git(string root, params string[] arguments)
    {
        var start = new ProcessStartInfo("git") { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        using var process = Process.Start(start) ?? throw new IOException("cannot start git");
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        if (process.ExitCode != 0) throw new IOException(stderr.GetAwaiter().GetResult());
        return stdout.GetAwaiter().GetResult().Trim();
    }
}
