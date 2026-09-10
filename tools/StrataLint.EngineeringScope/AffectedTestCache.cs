using System.Runtime.InteropServices;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record TestSuccessSource(string Candidate, string Round, string RunId, string RunAttempt,
    string Repository, string ActionIdentity, int Covered, ExecutionMaterial[] Trx);
internal sealed record TestActionCoverage(string Scope, string Status, string Reason, string Identity,
    int Covered, string[] Results, TestSuccessSource Source);
internal sealed record CachedTestSuccess(string Project, string Scope, string Identity, TestSuccessSource Source);
internal sealed record TestSuccessSeed(int Version, string Partition, TestInputManifest Manifest, CachedTestSuccess[] Successes);

internal sealed class AffectedTestCache
{
    internal const string CachePath = ".lake/test-cache";
    private readonly string root;
    private readonly TextWriter output;
    private readonly string? directory;
    private readonly string? partition;
    private readonly Dictionary<string, TestResultEvidence> evidence = new(StringComparer.Ordinal);
    private readonly Dictionary<string, string> hashes = new(StringComparer.Ordinal);
    private readonly HashSet<string> restored = new(StringComparer.Ordinal);
    internal TestSuccessSeed? Seed { get; }
    internal string MissReason { get; } = "cold-seed";

    internal AffectedTestCache(string root, TextWriter output)
    {
        this.root = root; this.output = output;
        try
        {
            var pins = LeanPinSet.Create([], File.ReadAllBytes(Path.Combine(root, "lake-manifest.json")));
            var os = OperatingSystem.IsMacOS() ? "darwin" : OperatingSystem.IsWindows() ? "windows" : "linux";
            partition = pins.MathlibRevision + "/" + os + "-" + RuntimeInformation.ProcessArchitecture.ToString().ToLowerInvariant();
            directory = Path.Combine(Environment.GetEnvironmentVariable("STRATALINT_TEST_CACHE_ROOT") ?? Path.Combine(root, CachePath), partition);
            var path = Path.Combine(directory, "seed.json");
            if (!File.Exists(path)) return;
            if (CommonExecutionEvidence.Hash(path) != File.ReadAllText(path + ".sha256").Trim()) throw new InvalidDataException("seed checksum mismatch");
            var seed = CommonExecutionEvidence.Read<TestSuccessSeed>(directory, "seed.json");
            AffectedTestPlan.Validate(seed.Manifest);
            if (seed.Version != 1 || seed.Partition != partition
                || seed.Successes.Any(success => !seed.Manifest.Actions.Any(action => action.Project == success.Project
                    && action.Scope == success.Scope && action.Identity == success.Identity && success.Source.ActionIdentity == action.Identity))
                || seed.Successes.Select(success => (success.Project, success.Scope)).Distinct().Count() != seed.Successes.Length)
                throw new InvalidDataException("seed identity mismatch");
            Seed = seed;
        }
        catch (Exception exception) when (CacheFailure(exception))
        { MissReason = "unusable-seed:" + exception.Message; output.WriteLine("ENGINEERING_CACHE miss=" + System.Text.Json.JsonSerializer.Serialize(MissReason)); }
    }

    internal (CachedTestSuccess? Success, string Reason) Select(TestAction action, TestProjectInputs? projectInputs = null)
    {
        if (action.Unknown.Length != 0) return (null, "unknown:" + string.Join(";", action.Unknown));
        if (Seed is null) return (null, MissReason);
        try
        {
            var previous = Seed.Manifest.Actions.SingleOrDefault(item => item.Project == action.Project && item.Scope == action.Scope);
            if (previous is null) return (null, "new-test-scope");
            if (previous.Producer != action.Producer) return (null, "producer-changed");
            if (previous.Environment != action.Environment) return (null, "environment-changed");
            if (previous.Identity != action.Identity)
            {
                var before = previous.Inputs.Concat(Seed.Manifest.Projects.Single(project => project.Project == action.Project).Inputs).ToDictionary(input => input.Path, input => input.Identity, StringComparer.Ordinal);
                var after = (projectInputs is null ? action.Inputs : action.Inputs.Concat(projectInputs.Inputs)).ToDictionary(input => input.Path, input => input.Identity, StringComparer.Ordinal);
                var changes = before.Keys.Union(after.Keys, StringComparer.Ordinal).Where(path => before.GetValueOrDefault(path) != after.GetValueOrDefault(path));
                return (null, "inputs-changed:" + string.Join(';', changes.Order(StringComparer.Ordinal))
                    + ";removed-edges:" + string.Join(';', previous.Edges.Concat(Seed.Manifest.Projects.Single(project => project.Project == action.Project).Edges).Except(action.Edges.Concat(projectInputs?.Edges ?? []), StringComparer.Ordinal)));
            }
            var success = Seed.Successes.SingleOrDefault(item => item.Project == action.Project && item.Scope == action.Scope
                && item.Identity == action.Identity);
            if (success is null) return (null, "missing-success-coverage");
            ValidateSource(action, success.Source, success.Source.Trx.Select(material => CachedPath(material.Sha256)).ToArray(), Load, hash: Hash);
            return (success, "validated-unchanged-inputs");
        }
        catch (Exception exception) when (CacheFailure(exception)) { return (null, "unusable-success:" + exception.Message); }
    }

    internal string[] Restore(CachedTestSuccess success)
    {
        var paths = new List<string>();
        foreach (var material in success.Source.Trx)
        {
            var relative = CommonExecutionEvidence.RootPath + "/reused-trx/" + material.Sha256 + "/source.trx";
            var destination = Path.Combine(root, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            if (!restored.Contains(relative))
            {
                var bytes = File.ReadAllBytes(CachedPath(material.Sha256));
                if (Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes)) != material.Sha256)
                    throw new InvalidDataException("cache material changed during restore");
                File.WriteAllBytes(destination, bytes);
                restored.Add(relative);
            }
            paths.Add(relative);
        }
        return paths.ToArray();
    }

    internal void Save(TestInputManifest manifest, IEnumerable<CachedTestSuccess> successes)
    {
        if (directory is null || partition is null) return;
        // This is local computation memory. Remote publishing remains the existing
        // Actions save gate, which is restore-only for PR callers.
        try
        {
            Directory.CreateDirectory(directory);
            var items = successes.ToArray();
            foreach (var trx in items.SelectMany(success => success.Source.Trx).DistinctBy(material => material.Sha256))
            {
                var target = CachedPath(trx.Sha256);
                if (File.Exists(target) && CommonExecutionEvidence.Hash(target) == trx.Sha256) continue;
                var source = Path.Combine(root, trx.Path);
                if (!File.Exists(source) || CommonExecutionEvidence.Hash(source) != trx.Sha256)
                    throw new InvalidDataException("success TRX disappeared before cache save");
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                var temporary = target + "." + Guid.NewGuid().ToString("N") + ".tmp";
                File.Copy(source, temporary);
                File.Move(temporary, target, overwrite: true);
            }
            var publication = "seed-" + Guid.NewGuid().ToString("N") + ".json";
            CommonExecutionEvidence.Write(directory, publication, new TestSuccessSeed(1, partition, manifest, items));
            var staged = Path.Combine(directory, publication);
            File.WriteAllText(staged + ".sha256", CommonExecutionEvidence.Hash(staged) + "\n");
            File.Move(staged, Path.Combine(directory, "seed.json"), overwrite: true);
            File.Move(staged + ".sha256", Path.Combine(directory, "seed.json.sha256"), overwrite: true);
            // Racing publications can yield a checksum miss, never reused coverage.

            var retained = items.SelectMany(item => item.Source.Trx).Select(material => material.Sha256).ToHashSet(StringComparer.Ordinal);
            var trxRoot = Path.Combine(directory, "trx");
            if (Directory.Exists(trxRoot))
                foreach (var previous in Directory.GetDirectories(trxRoot))
                    if (!retained.Contains(Path.GetFileName(previous))) Directory.Delete(previous, recursive: true);
            output.WriteLine($"ENGINEERING_CACHE status=saved successes={items.Length}");
        }
        catch (Exception exception) when (CacheFailure(exception))
        { output.WriteLine("ENGINEERING_CACHE status=save-failed reason=" + System.Text.Json.JsonSerializer.Serialize(exception.Message)); }
    }

    private string CachedPath(string hash) => Path.Combine(directory!, "trx", hash, "source.trx");
    private string Hash(string path)
    {
        if (!hashes.TryGetValue(path, out var hash)) hashes[path] = hash = CommonExecutionEvidence.Hash(path);
        return hash;
    }
    private TestResultEvidence Load(string path)
    {
        if (!evidence.TryGetValue(path, out var result)) evidence[path] = result = TestResultEvidence.Load(Path.GetDirectoryName(path)!);
        return result;
    }

    internal static void ValidateSource(TestAction action, TestSuccessSource source, string[] files, Func<string, TestResultEvidence>? load = null, bool requireComplete = true, Func<string, string>? hash = null)
    {
        if (source.Candidate.Length != 64 || !source.Candidate.All(char.IsAsciiHexDigit)
            || source.Round.Length != 32 || !source.Round.All(char.IsAsciiHexDigit)
            || string.IsNullOrWhiteSpace(source.RunId) || string.IsNullOrWhiteSpace(source.RunAttempt)
            || string.IsNullOrWhiteSpace(source.Repository)
            || source.Repository != (Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "local")
            || source.Trx.Any(material => material.Sha256.Length != 64 || !material.Sha256.All(char.IsAsciiHexDigit))
            || string.IsNullOrWhiteSpace(source.Candidate) || string.IsNullOrWhiteSpace(source.Round) || source.ActionIdentity != action.Identity
            || source.Covered < (requireComplete ? 1 : 0) || source.Trx.Length == 0 || source.Trx.Length != files.Length)
            throw new InvalidDataException("invalid original test success identity");
        var count = 0;
        var directories = new HashSet<string>(StringComparer.Ordinal);
        var methods = new HashSet<string>(StringComparer.Ordinal);
        for (var i = 0; i < files.Length; i++)
        {
            if ((hash ?? CommonExecutionEvidence.Hash)(files[i]) != source.Trx[i].Sha256) throw new InvalidDataException("original TRX integrity mismatch");
            if (!directories.Add(Path.GetDirectoryName(files[i])!)) continue;
            var trx = (load ?? (path => TestResultEvidence.Load(Path.GetDirectoryName(path)!)))(files[i]);
            if (trx.CountAssembly(action.Assembly) == 0) throw new InvalidDataException("original TRX belongs to a different test assembly");
            foreach (var method in action.Methods)
            {
                if (requireComplete && trx.SkippedMethods.Contains(method)) throw new InvalidDataException("original test method was skipped: " + method);
                var rows = trx.MethodCounts.GetValueOrDefault(method);
                count += rows;
                if (rows > 0 || !requireComplete && trx.SkippedMethods.Contains(method)) methods.Add(method);
            }
        }
        if (count != source.Covered || !action.Methods.All(methods.Contains))
            throw new InvalidDataException("original TRX does not cover the complete test scope");
    }

    internal static bool CacheFailure(Exception exception) => exception is InvalidDataException or IOException or UnauthorizedAccessException
        or System.Text.Json.JsonException or InvalidOperationException or ArgumentException or KeyNotFoundException
        or System.Xml.XmlException or FormatException or NullReferenceException;
}
