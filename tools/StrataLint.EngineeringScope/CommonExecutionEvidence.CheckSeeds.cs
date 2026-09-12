using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    private static Dictionary<string, CheckUnitResult> ImportCheckSeed(string root, string stage,
        RepositorySnapshot snapshot, IReadOnlyDictionary<string, string> inputs, TextWriter output)
    {
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
        foreach (var id in CheckIds(stage, ReadCheckManifest(snapshot)).Where(inputs.ContainsKey))
        {
            try
            {
                var row = rows.Single(row => row.ValueKind == JsonValueKind.Object && row.TryGetProperty("id", out var key) && key.GetString() == id);
                var unit = row.Deserialize<CheckUnitResult>(JsonOptions) ?? throw new InvalidDataException("missing common seed unit: " + id);
                if (unit.ExecutionEnvironment != ExecutionEnvironment(root))
                    throw new InvalidDataException("common seed execution environment differs from local environment: " + id);
                ValidateCheckUnit(seedRoot, root, snapshot, unit, inputs[id], candidate, round);
                foreach (var material in unit.Materials)
                {
                    var destination = Path.Combine(root, material.Path);
                    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                    // Identical original paths are shared by multiple units. A differing
                    // destination is a corrupt optional seed, never permission to overwrite.
                    if (File.Exists(destination))
                    {
                        if (Hash(destination) != material.Sha256) throw new InvalidDataException("conflicting original common material: " + material.Path);
                    }
                    else File.Copy(Path.Combine(seedRoot, material.Path), destination);
                }
                ValidateCheckUnit(root, root, snapshot, unit, inputs[id], candidate, round);
                accepted.Add(id, unit with { Status = "reused" });
                output.WriteLine($"COMMON_CHECK_REUSED id={id} execution_candidate={unit.ExecutionCandidate} execution_round={unit.ExecutionRound}");
            }
            catch (Exception exception) when (exception is InvalidDataException or FormatException or IOException or UnauthorizedAccessException or JsonException or InvalidOperationException or ArgumentException or KeyNotFoundException)
            {
                output.WriteLine($"COMMON_CHECK_SEED_MISS id={id} reason={JsonSerializer.Serialize(exception.Message)}");
            }
        }
        return accepted;
    }

    internal static bool ExportCheckSeed(string root, string stage, TextWriter output, string? destination = null)
    {
        // Acceptance errors are fatal; only optional copying/saving may fail harmlessly.
        _ = stage == "engineering" ? ValidateEngineering(root) : stage == "current" ? ValidateCurrent(root)
            : throw new InvalidDataException("invalid common seed stage: " + stage);
        var testMaterials = Array.Empty<string>();
        if (stage == "engineering" && destination is null)
        {
            var tests = ValidateTests(root);
            var seed = Path.Combine(root, TestSeedPath);
            var available = false;
            try
            {
                available = Hash(Path.Combine(seed, "tests.json")) == Hash(Path.Combine(root, TestsPath));
                if (available) ValidateMaterials(seed, tests.Materials);
            }
            catch (Exception exception) when (exception is InvalidDataException or IOException or UnauthorizedAccessException) { available = false; }
            if (available || ExportTestSeed(root, output))
                testMaterials = tests.Materials.Select(material => TestSeedPath + "/" + material.Path).Append(TestSeedPath + "/tests.json").ToArray();
        }
        return CopyCheckSeed(root, stage, output, destination, testMaterials);
    }

    private static bool CopyCheckSeed(string root, string stage, TextWriter output, string? destination, string[] testMaterials)
    {
        var record = ValidateChecks(root, stage, ValidateBuild(root), stage == "current" ? CurrentCheckIds(root) : null);
        destination ??= Path.Combine(root, CheckSeedPath(stage));
        var staging = destination + ".tmp-" + Guid.NewGuid().ToString("N");
        try
        {
            Directory.CreateDirectory(staging);
            var materials = record.Units.SelectMany(unit => unit.Materials).Distinct().ToArray();
            foreach (var material in materials)
            {
                var target = Path.Combine(staging, material.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Path.Combine(root, material.Path), target);
            }
            Write(staging, "checks.json", record);
            Write(staging, "materials.json", materials);
            ValidateMaterials(staging, materials);
            if (Directory.Exists(destination)) Directory.Delete(destination, recursive: true);
            Directory.Move(staging, destination);
            if (destination == Path.Combine(root, CheckSeedPath(stage)))
                WriteBundleList(root, stage + "-seed", materials.Select(material => CheckSeedPath(stage) + "/" + material.Path)
                    .Append(CheckSeedPath(stage) + "/checks.json").Append(CheckSeedPath(stage) + "/materials.json").Concat(testMaterials));
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

    internal static CommonCheckRecord ValidateCheckSeedBundle(string root, string stage)
    {
        var seed = Path.Combine(root, CheckSeedPath(stage));
        var record = Read<CommonCheckRecord>(seed, "checks.json");
        if (record.Version != 2 || record.Stage != stage || !ValidCandidate(record.Candidate) || !ValidRound(record.Round)
            || record.Units is null || record.Units.Any(unit => unit.Materials is null))
            throw new InvalidDataException("invalid common seed bundle identity");
        var materials = Read<ExecutionMaterial[]>(seed, "materials.json");
        if (!record.Units.SelectMany(unit => unit.Materials).Distinct().OrderBy(material => material.Path, StringComparer.Ordinal)
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
            var imported = ImportCheckSeed(root, stage, snapshot, CheckInputFingerprints(root, snapshot, currentReport: stage == "current"), output);
            output.WriteLine($"COMMON_CHECK_SEED_IMPORTED stage={stage} units={imported.Count}");
            if (stage == "engineering") _ = ImportTestSeed(root, TestInputs(root, snapshot), output);
        }
        return 0;
    }
}
