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
        var seedManifest = values.GetValueOrDefault("--seed-manifest");
        var required = new[] { "--repository", "--stage", "--commit", "--run-id", "--run-attempt" }
            .Concat(pack ? ["--archive"] : []).Concat(seedManifest is not null ? ["--seed-manifest"] : []).Order(StringComparer.Ordinal);
        if (!required.SequenceEqual(values.Keys.Order(StringComparer.Ordinal)))
            throw new ArgumentException("transport-pack|transport-verify --repository ROOT --stage build|engineering|current --commit SHA --run-id ID --run-attempt N [--archive FILE] [--seed-manifest FILE]");
        var root = Path.GetFullPath(values["--repository"]);
        var stage = values["--stage"];
        var commit = values["--commit"];
        if (stage is not ("build" or "engineering" or "current" or "engineering-seed" or "current-seed") || commit.Length != 40 || !commit.All(char.IsAsciiHexDigit)
            || !long.TryParse(values["--run-id"], NumberStyles.None, CultureInfo.InvariantCulture, out var run) || run < 1
            || !int.TryParse(values["--run-attempt"], NumberStyles.None, CultureInfo.InvariantCulture, out var attempt) || attempt < 1)
            throw new ArgumentException("invalid transport stage or immutable execution identity");
        var repository = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "";
        var seedStage = stage.EndsWith("-seed", StringComparison.Ordinal);
        if (seedManifest is not null && (!pack || stage is not ("engineering" or "current")))
            throw new ArgumentException("a companion seed manifest requires ordinary engineering or current pack");
        if (seedManifest is not null && Path.GetFullPath(seedManifest) == Path.GetFullPath(values["--archive"]))
            throw new ArgumentException("ordinary archive and seed manifest must have distinct destinations");
        if ((!seedStage || pack) && (Git(root, "rev-parse", "HEAD") != commit
            || Git(root, "status", "--porcelain", "--untracked-files=all").Length != 0))
            throw new InvalidDataException("transport requires the exact clean candidate commit");
        CommonStageRecord common;
        CommonStageRecord? build = null;
        CommonCheckRecord? checks = null;
        TestExecutionRecord? tests = null;
        CommonExecutionEvidence.ValidationScope? validation = null;
        if (seedStage)
        {
            var owner = stage[..^5];
            if (pack) _ = CommonExecutionEvidence.ExportCheckSeed(root, owner, output);
            var seed = CommonExecutionEvidence.ValidateCheckSeedBundle(root, owner);
            common = new(2, seed.Candidate, seed.Round, [], []);
        }
        else if (stage == "current")
            (common, build, validation, checks) = CommonExecutionEvidence.ValidateCurrentForTransport(root);
        else common = stage switch
        {
            "build" => CommonExecutionEvidence.ValidateBuild(root),
            _ => CommonExecutionEvidence.ValidateEngineering(root, out tests, out checks),
        };
        var manifestPath = ManifestPath(stage);
        if (pack)
        {
            var archive = Path.GetFullPath(values["--archive"]);
            PackArchive(stage, common, build, validation, archive);
            var outputs = new Dictionary<string, string>
            {
                ["artifact_name"] = ArtifactName(stage, run, attempt), ["archive"] = archive,
                ["run_id"] = run.ToString(CultureInfo.InvariantCulture), ["run_attempt"] = attempt.ToString(CultureInfo.InvariantCulture),
                ["commit"] = commit, ["candidate"] = common.Candidate, ["round"] = common.Round,
            };
            // The ordinary pack already accepted these records. Retain optional
            // materials before exposing output callbacks; imports still validate
            // them against their recipient's registered inputs and environment.
            using var messages = new StringWriter();
            if (seedManifest is not null && checks is not null)
            {
                var destination = Path.GetFullPath(seedManifest);
                try
                {
                    if (CommonExecutionEvidence.CopyAcceptedCheckSeed(root, stage, common, tests, checks, messages))
                    {
                        var seed = CommonExecutionEvidence.ValidateCheckSeedBundle(root, stage);
                        CopyManifest(stage + "-seed", new(2, seed.Candidate, seed.Round, [], []), destination);
                        outputs["seed_manifest"] = destination;
                    }
                }
                catch (Exception exception) when (exception is InvalidDataException or FormatException or IOException or UnauthorizedAccessException or ArgumentException)
                {
                    messages.WriteLine($"COMMON_CHECK_SEED_NOT_SAVED stage={stage} reason={System.Text.Json.JsonSerializer.Serialize(exception.Message)}");
                }
            }
            if (Environment.GetEnvironmentVariable("GITHUB_OUTPUT") is { Length: > 0 } destinationOutput)
                File.AppendAllLines(destinationOutput, outputs.Select(pair => pair.Key + "=" + pair.Value));
            output.Write(messages.ToString());
        }
        else
        {
            var record = CommonExecutionEvidence.Read<CiTransportRecord>(root, manifestPath);
            if (record.Version != 1 || record.Stage != stage || record.Candidate != common.Candidate || record.Round != common.Round
                || record.Commit != commit || record.RunId != run || record.RunAttempt != attempt || record.Repository != repository)
                throw new InvalidDataException("transport candidate, stage, or upstream execution mismatch");
            if (!ListedFiles(root, stage, common, build).Where(path => path != manifestPath).SequenceEqual(record.Materials.Select(material => material.Path)))
                throw new InvalidDataException("transport does not contain the complete stage file list");
            foreach (var material in record.Materials)
                if (MaterialHash(material.Path) != material.Sha256 || Mode(Path.Combine(root, material.Path)) != material.Mode)
                    throw new InvalidDataException("transport hash or mode mismatch: " + material.Path);
        }
        output.WriteLine($"CI_TRANSPORT stage={stage} candidate={common.Candidate} round={common.Round} commit={commit} run_id={run} run_attempt={attempt} status={(pack ? "packed" : "verified")}");
        return 0;

        TransportMaterial[] SealTransport(string packedStage, CommonStageRecord accepted, CommonStageRecord? acceptedBuild,
            CommonExecutionEvidence.ValidationScope? hashes)
        {
            var packedManifest = ManifestPath(packedStage);
            var paths = ListedFiles(root, packedStage, accepted, acceptedBuild).Where(path => path != packedManifest).ToArray();
            var materials = paths.Select(path => new TransportMaterial(path,
                hashes is null ? CommonExecutionEvidence.Hash(Path.Combine(root, path)) : hashes.Hash(Path.Combine(root, path)),
                Mode(Path.Combine(root, path)))).ToArray();
            CommonExecutionEvidence.Write(root, packedManifest, new CiTransportRecord(1, packedStage, accepted.Candidate, accepted.Round,
                commit, run, attempt, repository, materials));
            return materials;
        }

        void CopyManifest(string packedStage, CommonStageRecord accepted, string destination)
        {
            if (destination.StartsWith(Path.Combine(root, CommonExecutionEvidence.RootPath) + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                throw new ArgumentException("seed manifest must be outside the stage evidence directory");
            if (Directory.Exists(destination) || File.Exists(destination))
                throw new IOException("seed manifest already exists");
            SealTransport(packedStage, accepted, null, null);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            var temporary = destination + ".tmp-" + Guid.NewGuid().ToString("N");
            try
            {
                File.Copy(Path.Combine(root, ManifestPath(packedStage)), temporary);
                File.Move(temporary, destination);
            }
            finally
            {
                if (File.Exists(temporary)) File.Delete(temporary);
            }
        }

        void PackArchive(string packedStage, CommonStageRecord accepted, CommonStageRecord? acceptedBuild,
            CommonExecutionEvidence.ValidationScope? hashes, string archive)
        {
            if (archive.StartsWith(Path.Combine(root, CommonExecutionEvidence.RootPath) + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                throw new ArgumentException("archive must be outside the stage evidence directory");
            var materials = SealTransport(packedStage, accepted, acceptedBuild, hashes);
            var packedManifest = ManifestPath(packedStage);
            Directory.CreateDirectory(Path.GetDirectoryName(archive)!);
            using (var file = File.Create(archive + ".tmp"))
            using (var gzip = new GZipStream(file, CompressionLevel.Fastest))
            using (var tar = new TarWriter(gzip))
            {
                var stored = new Dictionary<(string Sha256, int Mode), string>();
                foreach (var material in materials)
                {
                    var path = Path.Combine(root, material.Path);
                    var identity = (material.Sha256, material.Mode);
                    if (!packedStage.EndsWith("-seed", StringComparison.Ordinal) && stored.TryGetValue(identity, out var original))
                        tar.WriteEntry(new PaxTarEntry(TarEntryType.HardLink, material.Path)
                        {
                            LinkName = original, Mode = (UnixFileMode)material.Mode,
                            ModificationTime = File.GetLastWriteTimeUtc(path),
                        });
                    else
                    {
                        tar.WriteEntry(path, material.Path);
                        stored.TryAdd(identity, material.Path);
                    }
                }
                tar.WriteEntry(Path.Combine(root, packedManifest), packedManifest);
            }
            File.Move(archive + ".tmp", archive, overwrite: true);
        }

        string MaterialHash(string path) => validation is null ? CommonExecutionEvidence.Hash(Path.Combine(root, path))
            : validation.Hash(Path.Combine(root, path));
    }

    private static string[] ListedFiles(string root, string stage, CommonStageRecord common, CommonStageRecord? build)
    {
        var text = File.ReadAllText(Path.Combine(root, CommonExecutionEvidence.BundleListPath(stage)));
        if (!text.EndsWith('\0')) throw new InvalidDataException("stage transport list is not NUL terminated");
        var declared = text.Split('\0', StringSplitOptions.RemoveEmptyEntries);
        if (!stage.EndsWith("-seed", StringComparison.Ordinal))
        {
            var materials = stage == "current" ? (build ?? throw new InvalidDataException("missing validated current build")).Materials.Concat(common.Materials)
                : common.Materials.Where(material => stage != "engineering" || material.Path != CommonExecutionEvidence.BuildPath);
            var expected = CommonExecutionEvidence.CanonicalBundlePaths(root, stage,
                materials.Select(material => material.Path).Append(CommonExecutionEvidence.RootPath + "/" + stage + ".json"));
            if (!declared.SequenceEqual(expected)) throw new InvalidDataException("transport list differs from the canonical stage obligations");
        }
        var summary = CommonExecutionEvidence.RootPath + "/" + stage + "-result.json";
        return declared
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
