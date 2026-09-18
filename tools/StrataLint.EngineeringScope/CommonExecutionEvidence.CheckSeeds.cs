using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record ProducerReportSeed(int Version, string Candidate, string Round, string Report, ExecutionMaterial[] Materials);

internal static partial class CommonExecutionEvidence
{
    private const string ProducerReportSeedPath = "producer-report.json";

    private static Dictionary<string, CheckUnitResult> ImportCheckSeed(string root, string stage,
        ValidationScope registration, IReadOnlyDictionary<string, string> inputs, TextWriter output)
    {
        var snapshot = registration.Snapshot;
        var accepted = new Dictionary<string, CheckUnitResult>(StringComparer.Ordinal);
        var seedRoot = Path.Combine(root, CheckSeedPath(stage));
        JsonElement document;
        JsonElement[] rows;
        string candidate;
        string round;
        try
        {
            document = Read<JsonElement>(seedRoot, "checks.json");
            if (!document.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal)
                .SequenceEqual(new[] { "candidate", "round", "stage", "units", "version" })
                || document.GetProperty("version").GetInt32() != 2 || document.GetProperty("stage").GetString() != stage)
                throw new InvalidDataException("invalid common seed envelope");
            candidate = document.GetProperty("candidate").GetString()!;
            round = document.GetProperty("round").GetString()!;
            if (!ValidCandidate(candidate) || !ValidRound(round)) throw new InvalidDataException("invalid common seed acceptance identity");
            rows = document.GetProperty("units").EnumerateArray().ToArray();
        }
        catch (Exception exception) when (exception is InvalidDataException or FormatException or IOException or UnauthorizedAccessException or JsonException or InvalidOperationException or KeyNotFoundException)
        {
            output.WriteLine($"COMMON_CHECK_SEED_UNAVAILABLE stage={stage} reason={JsonSerializer.Serialize(exception.Message)}");
            return accepted;
        }
        // Notifications can invoke caller code. Finish validation and copying before
        // exposing them, and never carry a validation scope across those writes.
        using var messages = new StringWriter();
        var sources = new List<CheckUnitResult>();
        var copied = new List<CheckUnitResult>();
        var environment = ExecutionEnvironment(root);
        var successfulReport = new ReportValidation(snapshot);
        {
            var validation = registration.Fresh(successfulReport);
            foreach (var id in CheckIds(stage, validation.CheckManifest()).Where(inputs.ContainsKey))
                Attempt(id, () =>
                {
                    var row = rows.Single(row => row.ValueKind == JsonValueKind.Object && row.TryGetProperty("id", out var key) && key.GetString() == id);
                    var unit = row.Deserialize<CheckUnitResult>(JsonOptions) ?? throw new InvalidDataException("missing common seed unit: " + id);
                    if (unit.ExecutionEnvironment != environment)
                        throw new InvalidDataException("common seed execution environment differs from local environment: " + id);
                    ValidateCheckUnit(seedRoot, root, snapshot, unit, inputs[id], candidate, round, validation);
                    sources.Add(unit);
                });
        }
        var destinations = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var unit in sources)
            Attempt(unit.Id, () =>
            {
                foreach (var material in unit.Materials)
                {
                    // Identical original paths are shared by multiple units. A differing
                    // destination is a corrupt optional seed, never permission to overwrite.
                    if (!destinations.TryGetValue(material.Path, out var actual))
                    {
                        var destination = Path.Combine(root, material.Path);
                        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                        if (File.Exists(destination)) actual = Hash(destination);
                        else
                        {
                            File.Copy(Path.Combine(seedRoot, material.Path), destination);
                            actual = material.Sha256;
                        }
                        destinations.Add(material.Path, actual);
                    }
                    if (actual != material.Sha256) throw new InvalidDataException("conflicting original common material: " + material.Path);
                }
                copied.Add(unit);
            });
        {
            var validation = registration.Fresh(successfulReport);
            foreach (var unit in copied)
                Attempt(unit.Id, () =>
                {
                    ValidateCheckUnit(root, root, snapshot, unit, inputs[unit.Id], candidate, round, validation);
                    accepted.Add(unit.Id, unit with { Status = "reused" });
                    messages.WriteLine($"COMMON_CHECK_REUSED id={unit.Id} execution_candidate={unit.ExecutionCandidate} execution_round={unit.ExecutionRound}");
                });
        }
        output.Write(messages.ToString());
        return accepted;

        void Attempt(string id, Action action)
        {
            try { action(); }
            catch (Exception exception) when (exception is InvalidDataException or FormatException or IOException or UnauthorizedAccessException or JsonException or InvalidOperationException or ArgumentException or KeyNotFoundException)
            {
                messages.WriteLine($"COMMON_CHECK_SEED_MISS id={id} reason={JsonSerializer.Serialize(exception.Message)}");
            }
        }
    }

    internal static bool ExportCheckSeed(string root, string stage, TextWriter output, string? destination = null)
    {
        // Acceptance errors are fatal; only optional copying/saving may fail harmlessly.
        CommonCheckRecord? checks = null;
        TestExecutionRecord? tests = null;
        var common = stage == "engineering" ? ValidateEngineering(root, out tests, out checks) : stage == "current" ? ValidateCurrent(root, out checks)
            : throw new InvalidDataException("invalid common seed stage: " + stage);
        return CopyAcceptedCheckSeed(root, stage, common, tests, checks, output, destination);
    }

    internal static bool CopyAcceptedCheckSeed(string root, string stage, CommonStageRecord common, TestExecutionRecord? tests,
        CommonCheckRecord? checks, TextWriter output, string? destination = null)
    {
        // Copying consumes the accepted records, never their source hash scope.
        // Emit notifications only after both copies; output can invoke caller code.
        using var messages = new StringWriter();
        var testMaterials = Array.Empty<string>();
        if (tests is not null && destination is null)
        {
            var seed = Path.Combine(root, TestSeedPath);
            var available = false;
            try
            {
                var saved = Read<TestExecutionRecord>(seed, "tests.json");
                if (saved.Projects is null || saved.Materials is null || saved.Projects.Any(project => project is null)
                    || saved.Materials.Any(material => material is null)) throw new InvalidDataException("invalid saved test seed inventory");
                available = saved.Version == tests.Version && saved.Candidate == tests.Candidate && saved.Round == tests.Round
                    && saved.Projects.Where(project => tests.Projects.Any(selected => selected.Project == project.Project)).SequenceEqual(tests.Projects);
                if (available) ValidateMaterials(seed, saved.Materials);
            }
            catch (Exception exception) when (exception is InvalidDataException or IOException or UnauthorizedAccessException or JsonException) { available = false; }
            if (available || CopyTestSeed(root, tests, messages))
                testMaterials = Read<TestExecutionRecord>(seed, "tests.json").Materials
                    .Select(material => TestSeedPath + "/" + material.Path).Append(TestSeedPath + "/tests.json").ToArray();
        }
        return CopyCheckSeed(root, stage, common, output, destination, testMaterials, checks, messages.ToString());
    }

    private static bool CopyCheckSeed(string root, string stage, CommonStageRecord common, TextWriter output, string? destination, string[] testMaterials,
        CommonCheckRecord? accepted, string testNotification)
    {
        // Stage validation accepted these exact units, build, plan and registry.
        // Retention only copies optional data; import validates it when selected.
        // This is an optional cache inventory, not execution evidence. A tests-only
        // stage has no current check units; its actual TRX seed travels alongside it.
        var record = accepted ?? new CommonCheckRecord(2, stage, common.Candidate, common.Round, []);
        var registered = CheckIds(stage, Read<CommonCheckManifest>(root, CheckManifestPath).Checks);
        var selected = record.Units.Select(unit => unit.Id).ToHashSet(StringComparer.Ordinal);
        var sources = record.Units.Select(unit => (Unit: unit, Root: root)).ToList();
        // Producer acceptance is independent of reused check execution. Its
        // hashes come from the accepted stage, never from a fresh source read.
        var producer = stage == "current" && common.Steps.Any(step => step.Name == "lean-report")
            ? new ProducerReportSeed(1, common.Candidate, common.Round, ReportPath,
                common.Materials.Where(material => ReportPaths.Contains(material.Path)
                    || material.Path == ReportPath + ReportReuseSuffix).ToArray())
            : null;
        var producerRoot = root;
        using var notifications = new StringWriter();
        notifications.Write(testNotification);
        if (selected.Count < registered.Length || stage == "current" && producer is null)
        {
            try
            {
                var previous = ValidateCheckSeedBundle(root, stage, out var previousProducer);
                var retained = previous.Units.Where(unit => registered.Contains(unit.Id) && !selected.Contains(unit.Id)).ToArray();
                if (retained.Select(unit => unit.Id).Distinct(StringComparer.Ordinal).Count() != retained.Length)
                    throw new InvalidDataException("duplicate retained common check");
                foreach (var unit in retained) ValidateCheckProvenance(unit, previous.Candidate, previous.Round);
                var previousRoot = Path.Combine(root, CheckSeedPath(stage));
                sources.AddRange(retained.Select(unit => (unit with { Status = "reused" }, previousRoot)));
                if (producer is null)
                {
                    producer = previousProducer;
                    producerRoot = previousRoot;
                }
            }
            catch (Exception exception) when (exception is InvalidDataException or FormatException or IOException or UnauthorizedAccessException or JsonException)
            {
                notifications.WriteLine($"COMMON_CHECK_SEED_RETENTION_UNAVAILABLE stage={stage} reason={JsonSerializer.Serialize(exception.Message)}");
            }
        }
        record = record with { Units = sources.Select(source => source.Unit).OrderBy(unit => Array.IndexOf(registered, unit.Id)).ToArray() };
        destination ??= Path.Combine(root, CheckSeedPath(stage));
        var staging = destination + ".tmp-" + Guid.NewGuid().ToString("N");
        try
        {
            Directory.CreateDirectory(staging);
            if (producer is not null) ValidateProducerReportSeed(producer, stage);
            var groups = sources.SelectMany(source => source.Unit.Materials.Select(material => (Material: material, source.Root)))
                .Concat((producer?.Materials ?? []).Select(material => (Material: material, Root: producerRoot)))
                .GroupBy(source => source.Material.Path, StringComparer.Ordinal).ToArray();
            var materials = groups.Select(group => group.First().Material).ToArray();
            foreach (var group in groups)
            {
                var source = group.First();
                var material = source.Material;
                if (group.Any(item => item.Material != material))
                    throw new InvalidDataException("conflicting retained common material: " + material.Path);
                var target = Path.Combine(staging, material.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Path.Combine(source.Root, material.Path), target);
            }
            if (producer is not null)
            {
                Write(staging, ProducerReportSeedPath, producer);
                materials = materials.Append(new(ProducerReportSeedPath, Hash(Path.Combine(staging, ProducerReportSeedPath)))).ToArray();
            }
            Write(staging, "checks.json", record);
            Write(staging, "materials.json", materials);
            ValidateMaterials(staging, materials);
            if (Directory.Exists(destination)) Directory.Delete(destination, recursive: true);
            Directory.Move(staging, destination);
            if (destination == Path.Combine(root, CheckSeedPath(stage)))
                WriteBundleList(root, stage + "-seed", materials.Select(material => CheckSeedPath(stage) + "/" + material.Path)
                    .Append(CheckSeedPath(stage) + "/checks.json").Append(CheckSeedPath(stage) + "/materials.json").Concat(testMaterials));
            output.Write(notifications.ToString());
            output.WriteLine($"COMMON_CHECK_SEED_SAVED stage={stage}");
            return true;
        }
        catch (Exception exception) when (exception is InvalidDataException or FormatException or IOException or UnauthorizedAccessException)
        {
            output.WriteLine($"COMMON_CHECK_SEED_NOT_SAVED stage={stage} reason={JsonSerializer.Serialize(exception.Message)}");
            return false;
        }
        finally
        {
            try { if (Directory.Exists(staging)) Directory.Delete(staging, recursive: true); }
            catch (IOException) { }
            catch (UnauthorizedAccessException) { }
        }
    }

    internal static CommonCheckRecord ValidateCheckSeedBundle(string root, string stage) => ValidateCheckSeedBundle(root, stage, out _);

    private static CommonCheckRecord ValidateCheckSeedBundle(string root, string stage, out ProducerReportSeed? producer)
    {
        var seed = Path.Combine(root, CheckSeedPath(stage));
        var record = Read<CommonCheckRecord>(seed, "checks.json");
        if (record.Version != 2 || record.Stage != stage || !ValidCandidate(record.Candidate) || !ValidRound(record.Round)
            || record.Units is null || record.Units.Any(unit => unit is null || unit.Materials is null
                || unit.Materials.Any(material => material is null || material.Path is null)))
            throw new InvalidDataException("invalid common seed bundle identity");
        var materials = Read<ExecutionMaterial[]>(seed, "materials.json");
        producer = ReadProducerReportSeed(seed, stage);
        var required = record.Units.SelectMany(unit => unit.Materials).Concat(producer?.Materials ?? []);
        if (producer is not null)
            required = required.Append(new(ProducerReportSeedPath, Hash(Path.Combine(seed, ProducerReportSeedPath))));
        if (materials is null || materials.Any(material => material is null || material.Path is null)
            || !required.Distinct().OrderBy(material => material.Path, StringComparer.Ordinal)
            .SequenceEqual(materials.OrderBy(material => material.Path, StringComparer.Ordinal)))
            throw new InvalidDataException("common seed material manifest mismatch");
        ValidateMaterials(seed, materials);
        var expected = materials.Select(material => Path.Combine(seed, material.Path))
            .Append(Path.Combine(seed, "checks.json"))
            .Append(Path.Combine(seed, "materials.json"))
            .Select(path => Path.GetFullPath(path))
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actual = Directory.GetFiles(seed, "*", SearchOption.AllDirectories)
            .Select(Path.GetFullPath)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (!actual.SequenceEqual(expected))
            throw new InvalidDataException("common seed contains extra or missing material");
        return record;
    }

    private static ProducerReportSeed? ReadProducerReportSeed(string seed, string stage)
    {
        if (!File.Exists(Path.Combine(seed, ProducerReportSeedPath))) return null;
        var producer = Read<ProducerReportSeed>(seed, ProducerReportSeedPath);
        ValidateProducerReportSeed(producer, stage);
        return producer;
    }

    private static void ValidateProducerReportSeed(ProducerReportSeed producer, string stage)
    {
        if (stage != "current" || producer.Version != 1 || !ValidCandidate(producer.Candidate) || !ValidRound(producer.Round)
            || producer.Report != ReportPath || producer.Materials is null
            || producer.Materials.Any(material => material is null || material.Path is null)
            || producer.Materials.Select(material => material.Path).Distinct(StringComparer.Ordinal).Count() != producer.Materials.Length
            || ReportPaths.Any(path => !producer.Materials.Any(material => material.Path == path))
            || producer.Materials.Any(material => !ReportPaths.Contains(material.Path) && material.Path != ReportPath + ReportReuseSuffix))
            throw new InvalidDataException("invalid current producer report seed");
    }

    internal static int CheckSeedCommand(IReadOnlyList<string> arguments, TextWriter output)
    {
        if (arguments.Count != 5 || arguments[1] != "--repository" || arguments[3] != "--stage"
            || arguments[4] is not ("engineering" or "current"))
            throw new ArgumentException("check-seed-export|check-seed-import --repository ROOT --stage engineering|current");
        var root = Path.GetFullPath(arguments[2]);
        var stage = arguments[4];
        if (arguments[0] == "check-seed-export") _ = ExportCheckSeed(root, stage, output);
        else
        {
            var snapshot = Snapshot(root);
            var validation = new ValidationScope(snapshot);
            var inputs = CheckInputFingerprints(root, snapshot, currentReport: stage == "current", validation: validation);
            var imported = ImportCheckSeed(root, stage, validation, inputs, output);
            output.WriteLine($"COMMON_CHECK_SEED_IMPORTED stage={stage} units={imported.Count}");
            if (stage == "engineering") _ = ImportTestSeed(root, TestInputs(root, snapshot), output);
        }
        return 0;
    }
}
