using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record CheckOperation(string Name, int RawExit, string Output);
internal sealed record CheckWork(CheckOperation[] Operations, string? Data = null);
internal sealed record CheckUnitResult(string Id, string InputFingerprint, string Status, string Result,
    string ExecutionCandidate, string ExecutionRound, StageStep[] Operations,
    string? Data, string? Report, ExecutionMaterial[] Materials);
internal sealed record CommonCheckRecord(int Version, string Stage, string Candidate, string Round, CheckUnitResult[] Units);
internal sealed record CheckDiagnostic(string Rule, string Title, DisplaySeverity Severity, AdmissionEffect Effect, string Path, string Message);
internal sealed record CurrentPredicateEvidence(string Rule, CheckDiagnostic[] Diagnostics);

internal static partial class CommonExecutionEvidence
{
    internal static readonly string[] EngineeringCheckIds = ["selftest-pair", "capability-proof", "banned-api-proof"];
    internal static string ChecksPath(string stage) => RootPath + "/" + stage + "-checks.json";
    internal static string CheckSeedPath(string stage) => RootPath + "/" + stage + "-check-seed";
    internal static string[] CheckIds(string stage, IEnumerable<RegisteredCommonCheck> checks) => stage switch
    {
        "engineering" => EngineeringCheckIds,
        "current" => checks.Select(check => check.Id).Except(EngineeringCheckIds).Order(StringComparer.Ordinal).ToArray(),
        _ => throw new InvalidDataException("invalid common check stage: " + stage),
    };

    internal static CheckExecution BeginChecks(string root, string stage, CommonStageRecord build, TextWriter output)
    {
        var snapshot = Snapshot(root);
        var registrations = ReadCheckManifest(snapshot);
        var inputs = CheckInputFingerprints(root, snapshot, currentReport: stage == "current");
        ValidateStartedBuild(root, build, Candidate(root));
        File.Delete(Path.Combine(root, ChecksPath(stage)));
        return new(root, stage, build, snapshot, registrations, inputs, output);
    }

    // This is the existing common owner, split by responsibility. Only a validated
    // instance may select engine predicates; callbacks execute already registered units.
    internal sealed class CheckExecution
    {
        private readonly string root;
        private readonly string stage;
        private readonly CommonStageRecord build;
        private readonly RepositorySnapshot snapshot;
        private readonly IReadOnlyList<RegisteredCommonCheck> registrations;
        private readonly IReadOnlyDictionary<string, string> inputs;
        private readonly Dictionary<string, CheckUnitResult> reused;
        private readonly Dictionary<string, CheckUnitResult> completed = new(StringComparer.Ordinal);
        private readonly string invocation;
        internal string[] Ids { get; }
        internal IReadOnlyCollection<CheckUnitResult> Completed => completed.Values;
        internal CheckExecution(string root, string stage, CommonStageRecord build, RepositorySnapshot snapshot,
            IReadOnlyList<RegisteredCommonCheck> registrations, IReadOnlyDictionary<string, string> inputs, TextWriter output)
        {
            this.root = root; this.stage = stage; this.build = build; this.snapshot = snapshot;
            this.registrations = registrations; this.inputs = inputs;
            Ids = CheckIds(stage, registrations);
            invocation = $"{RootPath}/check-material/{build.Candidate}/{build.Round}/{Guid.NewGuid():N}";
            reused = ImportCheckSeed(root, stage, snapshot, inputs, output);
        }
        internal bool IsSelected(string id) => Ids.Contains(id, StringComparer.Ordinal) && !reused.ContainsKey(id);
        internal CurrentRuleSelection SelectCurrentRules() => CurrentRuleSelection.Create(
            Ids.Where(id => id.StartsWith("SL-", StringComparison.Ordinal)).ToArray(),
            Ids.Where(id => id.StartsWith("SL-", StringComparison.Ordinal) && IsSelected(id)).ToArray());

        internal CheckUnitResult Run(string id, Func<CheckWork> execute)
        {
            if (!Ids.Contains(id, StringComparer.Ordinal) || completed.ContainsKey(id))
                throw new InvalidDataException("unregistered or duplicate common execution: " + id);
            if (reused.TryGetValue(id, out var previous))
            {
                completed.Add(id, previous);
                return previous;
            }
            // A selected callback or malformed current result is fatal. There is no seed
            // fallback after this point, and original files are never rewritten as current.
            var work = execute();
            if (work.Operations is null) throw new InvalidDataException("missing current operations: " + id);
            var directory = invocation + "/" + id;
            var operations = work.Operations.Select((operation, index) =>
            {
                var path = directory + "/" + index + ".log";
                Directory.CreateDirectory(Path.Combine(root, directory));
                File.WriteAllText(Path.Combine(root, path), operation.Output);
                return new StageStep(operation.Name, operation.RawExit, 0, "executed", path);
            }).ToArray();
            string? data = null;
            if (work.Data is not null)
            {
                data = directory + "/data.json";
                File.WriteAllText(Path.Combine(root, data), work.Data);
            }
            string? report = null;
            if (registrations.Single(check => check.Id == id).ReportInputs.Length != 0)
            {
                report = invocation + "/report/raw-lean-report.json";
                foreach (var path in ReportPaths)
                {
                    var target = Path.Combine(root, report + path[ReportPath.Length..]);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    if (!File.Exists(target)) File.Copy(Path.Combine(root, path), target);
                }
            }
            var materials = Materials(root, operations.Select(operation => operation.Log)
                .Concat(data is null ? [] : new[] { data })
                .Concat(report is null ? [] : ReportPaths.Select(path => report + path[ReportPath.Length..])));
            var unit = new CheckUnitResult(id, inputs[id], "executed", id == "selftest-pair" ? "equal" : "passed", build.Candidate, build.Round, operations, data, report, materials);
            ValidateCheckUnit(root, root, snapshot, unit, inputs[id], build.Candidate, build.Round);
            completed.Add(id, unit);
            return unit;
        }
        internal RuleExecutionOutcome ExecuteCurrentPredicates(ValidatedPolicy policy, AcceptedLeanClosure lean)
        {
            if (stage != "current") throw new InvalidDataException("current selection requires current owner");
            var verified = ReadScribe(root, completed.TryGetValue("scribe-describe", out var describe) ? describe
                : throw new InvalidDataException("current predicates require the completed Scribe producer"), snapshot);
            var evaluated = AdmissionPipeline.CheckCurrent(CurrentRuleContext.Create(snapshot, policy, lean, verified, SelectCurrentRules()));
            if (evaluated is not RuleExecutionOutcome.Completed complete) return evaluated;
            var actual = complete.Capability;
            var failed = new HashSet<string>(StringComparer.Ordinal);
            foreach (var id in Ids.Where(id => id.StartsWith("SL-", StringComparison.Ordinal)))
            {
                var diagnostics = actual.Diagnostics.Where(d => d.RuleId.Value == id || id == "SL-015" && d.RuleId.Value == "SL-000").ToArray();
                try
                {
                    Run(id, () =>
                    {
                        if (!actual.ExecutedRules.Any(rule => rule.Value == id)) throw new InvalidDataException("selected predicate did not execute: " + id);
                        return new([new(id, diagnostics.Any(d => d.AdmissionEffect != AdmissionEffect.Observe) ? 1 : 0, PredicateJson(id, diagnostics))]);
                    });
                }
                catch (InvalidDataException) when (diagnostics.Any(d => d.AdmissionEffect != AdmissionEffect.Observe)) { failed.Add(id); }
            }
            var diagnosticsCombined = PredicateDiagnostics(root, completed.Values).AddRange(actual.Diagnostics.Where(d => failed.Contains(d.RuleId.Value)
                || d.RuleId.Value == "SL-000" && failed.Contains("SL-015")));
            return new RuleExecutionOutcome.Completed(CompletedRuleSet.Create(
                diagnosticsCombined.OrderBy(d => d.RuleId.Value, StringComparer.Ordinal).ThenBy(d => d.Path, StringComparer.Ordinal)
                    .ThenBy(d => d.Message, StringComparer.Ordinal).ToImmutableArray(),
                actual.DeferredRules, actual.ExecutedRules, actual.SkippedRules));
        }

        internal CommonCheckRecord Seal()
        {
            var record = new CommonCheckRecord(1, stage, build.Candidate, build.Round,
                Ids.Select(id => completed.TryGetValue(id, out var unit) ? unit
                    : throw new InvalidDataException("required common unit did not run: " + id)).ToArray());
            ValidateStartedBuild(root, build, Candidate(root));
            ValidateCheckRecord(root, record, snapshot, inputs, build.Candidate, build.Round);
            Write(root, ChecksPath(stage), record);
            return record;
        }
    }

    internal static CommonCheckRecord ValidateChecks(string root, string stage, CommonStageRecord build)
    {
        var record = Read<CommonCheckRecord>(root, ChecksPath(stage));
        if (record.Stage != stage) throw new InvalidDataException("common check stage mismatch");
        var snapshot = Snapshot(root);
        ValidateCheckRecord(root, record, snapshot, CheckInputFingerprints(root, snapshot, currentReport: stage == "current"), build.Candidate, build.Round);
        return record;
    }
    private static void ValidateCheckRecord(string root, CommonCheckRecord record, RepositorySnapshot snapshot,
        IReadOnlyDictionary<string, string> inputs, string candidate, string round)
    {
        if (record.Version != 1 || !ValidCandidate(record.Candidate) || !ValidRound(record.Round) || record.Candidate != candidate || record.Round != round || record.Units is null || record.Units.Any(unit => unit is null))
            throw new InvalidDataException("common check candidate or round mismatch");
        var expected = CheckIds(record.Stage, ReadCheckManifest(snapshot));
        if (!expected.SequenceEqual(record.Units.Select(unit => unit.Id)))
            throw new InvalidDataException("missing, duplicated or unordered common check result");
        foreach (var unit in record.Units) ValidateCheckUnit(root, root, snapshot, unit, inputs[unit.Id], candidate, round);
    }
    private static void ValidateCheckUnit(string materialRoot, string sourceRoot, RepositorySnapshot snapshot,
        CheckUnitResult unit, string fingerprint, string candidate, string round)
    {
        if (unit.Operations is null || unit.Materials is null || unit.Operations.Any(operation => operation is null || operation.Log is null)
            || unit.Materials.Any(material => material is null || material.Path is null))
            throw new InvalidDataException("missing common unit materials: " + unit.Id);
        var registration = ReadCheckManifest(snapshot).Single(check => check.Id == unit.Id);
        if ((registration.ReportInputs.Length != 0) != (unit.Report is not null))
            throw new InvalidDataException("common report declaration/material mismatch: " + unit.Id);
        if (unit.Result != (unit.Id == "selftest-pair" ? "equal" : "passed") || unit.InputFingerprint != fingerprint || unit.Status is not ("executed" or "reused")
            || !ValidCandidate(unit.ExecutionCandidate) || !ValidRound(unit.ExecutionRound)
            || unit.Status == "executed" && (unit.ExecutionCandidate != candidate || unit.ExecutionRound != round)
            || unit.Operations is null || unit.Materials is null)
            throw new InvalidDataException("invalid common check identity/provenance: " + unit.Id);
        var prefix = $"{RootPath}/check-material/{unit.ExecutionCandidate}/{unit.ExecutionRound}/";
        var required = unit.Operations.Select(operation => operation.Log).Concat(unit.Data is null ? [] : new[] { unit.Data })
            .Concat(unit.Report is null ? [] : ReportPaths.Select(path => unit.Report + path[ReportPath.Length..])).Order(StringComparer.Ordinal).ToArray();
        if (required.Length == 0 || required.Distinct(StringComparer.Ordinal).Count() != required.Length
            || !required.SequenceEqual(unit.Materials.Select(material => material.Path).Order(StringComparer.Ordinal))
            || required.Any(path => !path.StartsWith(prefix, StringComparison.Ordinal)))
            throw new InvalidDataException("missing or contradictory common material: " + unit.Id);
        ValidateMaterials(materialRoot, unit.Materials);
        var operations = unit.Operations;
        string Log(int index) => File.ReadAllText(Path.Combine(materialRoot, operations[index].Log));
        bool Names(params string[] names) => names.SequenceEqual(operations.Select(operation => operation.Name));
        if (operations.Any(operation => operation.Status != "executed" || operation.Exit != 0))
            throw new InvalidDataException("failed original common operation: " + unit.Id);
        var accepted = unit.Id switch
        {
            "selftest-pair" => Names("selftest-first", "selftest-second") && operations.All(operation => operation.RawExit == 0)
                && Log(0).Contains("SELFTEST PASS", StringComparison.Ordinal) && Log(0) == Log(1),
            "capability-proof" => Names("restore-CompileFailProof", unit.Id) && operations[0].RawExit == 0
                && CompilationProof.ValidateCapability(operations[1].RawExit, Log(1)),
            "banned-api-proof" => Names("restore-BannedApiCompileFailProof", unit.Id) && operations[0].RawExit == 0
                && CompilationProof.ValidateBannedApi(operations[1].RawExit, Log(1),
                    File.ReadAllText(Path.Combine(sourceRoot, "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"))),
            _ => Names(unit.Id) && operations[0].RawExit == 0,
        };
        if (!accepted) throw new InvalidDataException("common check validation failed: " + unit.Id);
        if (unit.Report is not null)
        {
            _ = RawLeanReportArtifact.ReadFile(Path.Combine(materialRoot, unit.Report), snapshot, validateMaterials: true);
            if (Hash(Path.Combine(materialRoot, unit.Report)) != Hash(Path.Combine(sourceRoot, ReportPath)))
                throw new InvalidDataException("original common report differs from current validated report: " + unit.Id);
        }
        if (unit.Id.StartsWith("SL-", StringComparison.Ordinal)) _ = ReadPredicate(materialRoot, unit);
        if (unit.Id == "scribe-describe") _ = ReadScribe(materialRoot, unit, snapshot);
    }

    internal static CurrentPredicateEvidence ReadPredicate(string root, CheckUnitResult unit)
    {
        var result = Read<CurrentPredicateEvidence>(root, unit.Operations.Single().Log);
        if (result.Rule != unit.Id || result.Diagnostics is null || result.Diagnostics.Any(diagnostic => diagnostic is null || diagnostic.Rule != unit.Id && !(unit.Id == "SL-015" && diagnostic.Rule == "SL-000")
            || string.IsNullOrEmpty(diagnostic.Title) || diagnostic.Path is null || diagnostic.Message is null
            || !Enum.IsDefined(diagnostic.Severity) || diagnostic.Effect != AdmissionEffect.Observe))
            throw new InvalidDataException("invalid or failed current predicate result: " + unit.Id);
        return result;
    }
    internal static VerifiedScribeEmissions ReadScribe(string root, CheckUnitResult unit, RepositorySnapshot snapshot)
    {
        if (unit.Id != "scribe-describe" || unit.Data is null) throw new InvalidDataException("missing validated Scribe material");
        return VerifiedScribeEmissions.ReadMaterial(File.ReadAllText(Path.Combine(root, unit.Data)), snapshot);
    }
    internal static string PredicateJson(string id, IEnumerable<Diagnostic> diagnostics) => JsonSerializer.Serialize(
        new CurrentPredicateEvidence(id, diagnostics.Select(d => new CheckDiagnostic(d.RuleId.Value, d.Title, d.DisplaySeverity, d.AdmissionEffect, d.Path, d.Message)).ToArray()), JsonOptions);
    internal static ImmutableArray<Diagnostic> PredicateDiagnostics(string root, IEnumerable<CheckUnitResult> units) => units
        .Where(unit => unit.Id.StartsWith("SL-", StringComparison.Ordinal)).SelectMany(unit => ReadPredicate(root, unit).Diagnostics)
        .Select(d => new Diagnostic(RuleId.CreateKnown(int.Parse(d.Rule.AsSpan(3), System.Globalization.CultureInfo.InvariantCulture)), d.Title, d.Severity, d.Effect, d.Path, d.Message)).ToImmutableArray();
}
