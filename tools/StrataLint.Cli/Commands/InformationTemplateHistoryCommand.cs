using System.Collections.Immutable;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal interface IInformationTemplateHistoryRepository
{
    string CurrentRevision { get; }
    string ResolveBase(string? revision);
    RawRepositorySnapshot ReadPredicate(string? revision);
    RawRepositorySnapshot ReadCandidate();
    RawRepositorySnapshot ReadHistorical(string revision);
}

internal static class InformationTemplateHistoryCommand
{
    private static readonly JsonSerializerOptions Wire = new() { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower };
    private sealed record PlanFile(string Schema, string Candidate, string Os, string Arch, bool Required,
        string ProtectedBase, string Purpose, string? Producer, ImmutableArray<InformationTemplateHistoryTarget> Targets,
        InformationTemplateHistoryTarget? Adoption, string? JudgeAddress, string? ConfigAddress);

    internal static CommandResult Run(string root, IInformationTemplateHistoryRepository repository,
        IReadOnlyList<string> arguments, IGitProcessRunner runner, TimeProvider clock)
    {
        var started = clock.GetTimestamp();
        var timings = new Dictionary<string, double>(StringComparer.Ordinal);
        void Timed(string phase, Action action)
        {
            var phaseStart = clock.GetTimestamp();
            try { action(); }
            finally { timings[phase] = timings.GetValueOrDefault(phase) + clock.GetElapsedTime(phaseStart).TotalMilliseconds; }
        }
        try
        {
            if (arguments.Count == 0 || arguments[0] is not ("plan" or "prepare" or "produce" or "validate" or "adopt"))
                throw new FormatException("information-template-history requires plan, prepare, produce, validate or adopt");
            var options = Options(arguments);
            string Required(string name) => options.TryGetValue(name, out var value) ? value
                : throw new FormatException("history requires " + name);
            InformationTemplateHistoryInputs? inputs = null;
            RawRepositorySnapshot? candidate = null;
            InformationTemplateHistoryInputs Inputs() => inputs ??= new(candidate ??= repository.ReadCandidate());
            var historical = new Dictionary<string, RawRepositorySnapshot>(StringComparer.Ordinal);
            RawRepositorySnapshot Historical(string revision)
            {
                if (!historical.TryGetValue(revision, out var snapshot)) historical.Add(revision, snapshot = repository.ReadHistorical(revision));
                return snapshot;
            }
            PlanFile Build(string? requestedBase, string purpose, string os, string arch, string? judgeAddress, string? configAddress)
            {
                if (judgeAddress is not null) InformationTemplateJson.Hash(judgeAddress, 64);
                if (configAddress is not null) InformationTemplateJson.Hash(configAddress, 64);
                var revision = repository.ResolveBase(requestedBase);
                var plan = InformationTemplateHistoryPlan.Create(revision,
                    InformationTemplateHistoryInputs.Decode(repository.ReadPredicate(revision)),
                    InformationTemplateHistoryInputs.Decode(repository.ReadPredicate(null)), purpose, () => Inputs().Producer, os, arch);
                foreach (var target in plan.Targets) Historical(target.Revision);
                var head = InformationTemplateJson.Hash(repository.CurrentRevision, 40);
                return new("information-template-history-plan-v1", head, os, arch, plan.Required, plan.ProtectedBase,
                    purpose, plan.Producer, plan.Targets, plan.Required ? InformationTemplateHistoryPlan.Target(plan.Producer!, head, os, arch) : null, judgeAddress, configAddress);
            }
            if (arguments[0] == "plan")
            {
                var plan = Build(options.GetValueOrDefault("--protected-base"), options.GetValueOrDefault("--purpose", "check"),
                    options.GetValueOrDefault("--os", OperatingSystem.IsMacOS() ? "macOS" : OperatingSystem.IsLinux() ? "Linux" : "Windows"),
                    options.GetValueOrDefault("--arch", RuntimeInformation.ProcessArchitecture.ToString().ToUpperInvariant()),
                    options.GetValueOrDefault("--judge-address"), options.GetValueOrDefault("--config-address"));
                var bytes = PlanBytes(plan);
                if (options.TryGetValue("--output", out var output)) Write(output, bytes);
                if (options.TryGetValue("--github-output", out var github))
                    File.AppendAllText(github, $"history_required={plan.Required.ToString().ToLowerInvariant()}\n"
                        + "history_matrix=" + JsonSerializer.Serialize(new { include = plan.Targets }, Wire) + "\n"
                        + $"history_producer={plan.Producer}\nhistory_adoption_key={plan.Adoption?.CacheKey}\n");
                return new(true, Encoding.UTF8.GetString(bytes.AsSpan()),
                    $"INFORMATION_TEMPLATE_HISTORY phase=plan required={plan.Required.ToString().ToLowerInvariant()} elapsed_ms={clock.GetElapsedTime(started).TotalMilliseconds:F3}\n");
            }
            using var stored = InformationTemplateJson.Read(File.ReadAllBytes(Required("--plan")));
            InformationTemplateJson.Fields(stored.RootElement, "schema", "candidate", "os", "arch", "required",
                "protected_base", "purpose", "producer", "targets", "adoption", "judge_address", "config_address");
            var saved = JsonSerializer.Deserialize<PlanFile>(stored.RootElement, Wire)
                ?? throw new FormatException("history plan is empty");
            var fresh = Build(saved.ProtectedBase, saved.Purpose, saved.Os, saved.Arch, saved.JudgeAddress, saved.ConfigAddress);
            if (!PlanBytes(fresh).AsSpan().SequenceEqual(PlanBytes(saved).AsSpan()) || !fresh.Required)
                throw new FormatException("history plan is stale or inactive");
            var revision = InformationTemplateJson.Hash(Required("--revision"), 40);
            var adopting = arguments[0] == "adopt";
            if (adopting ? revision != fresh.Candidate : !fresh.Targets.Any(t => t.Revision == revision))
                throw new FormatException("history revision is not authorized by this plan");
            if (adopting)
            {
                var checkedCommit = Historical(revision).Entries.ToDictionary(e => e.Path, StringComparer.Ordinal);
                if (candidate!.Entries.Length != checkedCommit.Count || candidate.Entries.Any(e => !e.IsTracked
                    || !checkedCommit.TryGetValue(e.Path, out var committed) || e.GitMode != committed.GitMode
                    || !e.Bytes.AsSpan().SequenceEqual(committed.Bytes.AsSpan())))
                    throw new FormatException("history adoption requires the actual clean checked commit");
            }
            var material = Inputs().Material(revision, Historical(revision));
            var producer = fresh.Producer!;
            var pair = InformationTemplateHistoryPlan.Target(producer, revision, fresh.Os, fresh.Arch).Pair;
            string Work() => options.TryGetValue("--work", out var path) ? Path.GetFullPath(path)
                : throw new FormatException("history prepare requires --work");
            if (arguments[0] == "prepare")
            {
                Timed("prepare", () => InformationTemplateHistoryWorkspace.Prepare(root, Work(), pair, revision, material.Files, runner));
                return Result("prepared", false);
            }
            if (arguments[0] == "validate")
            {
                var bundle = Path.GetFullPath(Required("--bundle"));
                Timed("validate", () => InformationTemplateHistoryBundle.Validate(bundle, producer, revision, material.Hybrid));
                if (options.TryGetValue("--output", out var destination))
                    Timed("publish", () => InformationTemplateHistoryWorkspace.Publish(bundle, destination));
                return Result("validated", true);
            }
            var outputDirectory = Path.GetFullPath(Required("--output"));
            var cacheRoot = Path.GetFullPath(options.GetValueOrDefault("--cache-root") ?? DefaultCache());
            var cache = Path.Combine(cacheRoot, producer, revision);
            using var mutex = new Mutex(false, "stratalint-it-history-" + pair);
            var acquired = false;
            try
            {
                try { acquired = mutex.WaitOne(TimeSpan.FromMinutes(60)); }
                catch (AbandonedMutexException) { acquired = true; }
                if (!acquired) throw new TimeoutException("history pair writer lock timed out");
                var invalid = false;
                if (!adopting)
                foreach (var directory in new[] { outputDirectory, cache }.Distinct(StringComparer.Ordinal))
                {
                    if (!Directory.Exists(directory)) continue;
                    try { Timed("cache_validate", () => InformationTemplateHistoryBundle.Validate(directory, producer, revision, material.Hybrid)); }
                    catch (Exception ex) when (ArtifactError(ex)) { invalid = true; continue; }
                    RequireUnchangedProducer();
                    InformationTemplateHistoryWorkspace.Publish(directory, outputDirectory);
                    return Result("hit", true);
                }
                var staging = Directory.CreateTempSubdirectory("stratalint-history-bundle-").FullName;
                string? ownedWork = null;
                try
                {
                    var report = Path.Combine(staging, InformationTemplateHistoryBundle.ReportName);
                    var producerOutput = "";
                    if (adopting)
                    {
                        var candidateReport = Path.GetFullPath(Required("--report"));
                        InformationTemplateHistoryBundle.ValidateReport(candidateReport, material.Hybrid);
                        InformationTemplateHistoryBundle.Copy(candidateReport, staging);
                    }
                    else
                    {
                        var work = options.TryGetValue("--work", out var requestedWork) ? Path.GetFullPath(requestedWork)
                            : ownedWork = Directory.CreateTempSubdirectory("stratalint-history-work-").FullName;
                        Timed("prepare", () => InformationTemplateHistoryWorkspace.Prepare(root, work, pair, revision, material.Files, runner));
                        if (options.TryGetValue("--cache-donor", out var donor))
                            Timed("cache_seed", () => InformationTemplateHistoryCacheSeed.Copy(work, donor));
                        var inspectorStart = clock.GetTimestamp();
                        var produced = runner.Run("/bin/bash", [Path.Combine(work, "tools/lean-inspector/inspect.sh"),
                            "--repository", work, "--output", report], work, TimeSpan.FromMinutes(60));
                        timings["inspector"] = clock.GetElapsedTime(inspectorStart).TotalMilliseconds;
                        producerOutput = Encoding.UTF8.GetString(produced.StandardOutput) + Encoding.UTF8.GetString(produced.StandardError);
                        if (produced.ExitCode != 0) throw new IOException($"history inspector exit={produced.ExitCode}\n" + producerOutput);
                    }
                    // A concurrent source edit cannot be published under the old P.
                    RequireUnchangedProducer();
                    Timed("seal_validate", () =>
                    {
                        InformationTemplateHistoryBundle.Seal(staging, producer, revision, material.Hybrid, fresh.Candidate,
                            options.GetValueOrDefault("--run", "local"));
                        InformationTemplateHistoryBundle.Validate(staging, producer, revision, material.Hybrid);
                    });
                    Timed("publish", () => InformationTemplateHistoryWorkspace.Publish(staging, outputDirectory));
                    var save = "saved";
                    try { if (cache != outputDirectory) Timed("cache_save", () => InformationTemplateHistoryWorkspace.Publish(staging, cache)); }
                    catch (Exception error) when (error is IOException or UnauthorizedAccessException)
                    { save = "save-failed"; producerOutput += "INFORMATION_TEMPLATE_HISTORY cache=save-failed detail=" + error.Message + "\n"; }
                    return Result(adopting ? "adopted" : invalid ? "rebuilt-invalid" : "produced", false, producerOutput, save);
                }
                finally
                {
                    Directory.Delete(staging, true);
                    if (ownedWork is not null) Directory.Delete(ownedWork, true);
                }
            }
            finally { if (acquired) mutex.ReleaseMutex(); }

            void RequireUnchangedProducer()
            {
                if (new InformationTemplateHistoryInputs(repository.ReadCandidate()).Producer != producer)
                    throw new IOException("history producer changed during production");
            }

            CommandResult Result(string status, bool hit, string detail = "", string cacheSave = "not-required") => new(true, detail + JsonSerializer.Serialize(new
            {
                schema = "information-template-history-result-v1", status, revision, producer, pair, cache_hit = hit,
                elapsed_ms = clock.GetElapsedTime(started).TotalMilliseconds, cache_save = cacheSave,
                timings_ms = timings,
                material_files = material.Files.Length, material_bytes = material.Files.Sum(f => (long)f.Bytes.Length),
            }) + "\n", "");
        }
        catch (Exception error) when (ArtifactError(error) || error is TimeoutException or ArgumentException or UnauthorizedAccessException)
        {
            return new(false, "", "information-template-history: " + error.Message + "\n");
        }
    }

    private static bool ArtifactError(Exception error) => error is IOException or FormatException or InvalidOperationException or JsonException
        or KeyNotFoundException;
    private static ImmutableArray<byte> PlanBytes(PlanFile plan) =>
        InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(plan, Wire));
    private static void Write(string path, ImmutableArray<byte> bytes)
    {
        path = Path.GetFullPath(path);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        var temporary = path + ".tmp-" + Guid.NewGuid().ToString("N");
        try { File.WriteAllBytes(temporary, bytes.AsSpan()); File.Move(temporary, path, true); }
        finally { if (File.Exists(temporary)) File.Delete(temporary); }
    }
    private static string DefaultCache() => Path.Combine(Environment.GetEnvironmentVariable("XDG_CACHE_HOME")
        ?? Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".cache"), "stratalint", "information-template-history");
    private static Dictionary<string, string> Options(IReadOnlyList<string> arguments)
    {
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        for (var i = 1; i < arguments.Count; i += 2)
            if (i + 1 >= arguments.Count || string.IsNullOrWhiteSpace(arguments[i + 1]) || arguments[i] is not
                ("--protected-base" or "--purpose" or "--output" or "--plan" or "--revision" or "--work" or "--bundle"
                or "--judge-address" or "--config-address" or "--report" or "--os" or "--arch" or "--github-output" or "--cache-root" or "--cache-donor" or "--run")
                || !result.TryAdd(arguments[i], arguments[i + 1]))
                throw new FormatException("invalid or duplicate history option");
        return result;
    }
}
