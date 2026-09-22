using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record CheckOperation(string Name, int RawExit, string Output);
internal sealed record CheckWork(CheckOperation[] Operations, string? Data = null);
internal sealed class CommonCheckFailure(StageStep operation, string diagnostic)
    : Exception($"COMMON_CHECK_FAILED {operation.Name}: raw_exit={operation.RawExit}; log={operation.Log}\n{diagnostic}")
{
    internal StageStep Operation { get; } = operation;
}
internal sealed record CheckUnitResult(string Id, string InputFingerprint, string Status, string Result,
    string ExecutionCandidate, string ExecutionRound, string ExecutionEnvironment, StageStep[] Operations,
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

    internal static CheckExecution BeginChecks(string root, string stage, CommonStageRecord build, TextWriter output,
        string[]? selectedIds = null, ValidationScope? validation = null)
    {
        validation ??= ValidationScope.Create(root);
        var snapshot = validation.Snapshot;
        var registrations = validation.CheckManifest();
        var ids = selectedIds ?? CheckIds(stage, registrations);
        if (ids.Distinct(StringComparer.Ordinal).Count() != ids.Length || ids.Except(CheckIds(stage, registrations)).Any())
            throw new InvalidDataException("unregistered selected common units");
        var environment = ExecutionEnvironment(root);
        var changedPaths = stage == "current" ? CurrentPlan(root, build)?.ChangedPaths : null;
        var fileMapScope = ids.Contains("filemap") ? FileMapInspectionScope.Select(
            registrations.Single(check => check.Id == "filemap").DeltaScope, changedPaths,
            snapshot.Files.Keys.Select(path => path.Value).ToArray()) : null;
        var markdown = registrations.Single(check => check.Id == "scribe-markdown");
        var markdownScope = ids.Contains("scribe-markdown") ? MarkdownInspectionScope.Select(markdown.MarkdownScope, changedPaths,
            snapshot.Files.Keys.Select(path => path.Value).ToArray(), markdown.PathInventory) : null;
        var inputs = CheckInputFingerprints(root, snapshot, currentReport: stage == "current", selectedIds: ids, executionEnvironment: environment,
            validation: validation, changedPaths: changedPaths);
        ValidateStartedBuild(root, build, Candidate(root, snapshot), validation);
        File.Delete(Path.Combine(root, ChecksPath(stage)));
        return new(root, stage, build, validation, registrations, inputs, environment, output, ids, fileMapScope, markdownScope);
    }

    // This is the existing common owner, split by responsibility. Only a validated
    // instance may select engine predicates; callbacks execute already registered units.
    internal sealed class CheckExecution
    {
        private readonly string root;
        private readonly string stage;
        private readonly CommonStageRecord build;
        private readonly RepositorySnapshot snapshot;
        private readonly ValidationScope registration;
        private readonly ReportValidation successfulReport;
        private readonly IReadOnlyList<RegisteredCommonCheck> registrations;
        private readonly IReadOnlyDictionary<string, string> inputs;
        private readonly string environment;
        private readonly Dictionary<string, CheckUnitResult> reused;
        private readonly Dictionary<string, CheckUnitResult> completed = new(StringComparer.Ordinal);
        private readonly string invocation;
        internal string[] Ids { get; }
        internal FileMapInspectionScope? FileMapScope { get; }
        internal MarkdownInspectionScope? MarkdownScope { get; }
        internal IReadOnlyCollection<CheckUnitResult> Completed => completed.Values;
        internal CheckExecution(string root, string stage, CommonStageRecord build, ValidationScope validation,
            IReadOnlyList<RegisteredCommonCheck> registrations, IReadOnlyDictionary<string, string> inputs, string environment, TextWriter output, string[] ids,
            FileMapInspectionScope? fileMapScope, MarkdownInspectionScope? markdownScope)
        {
            this.root = root; this.stage = stage; this.build = build; snapshot = validation.Snapshot;
            registration = validation.Fresh();
            successfulReport = new(snapshot);
            this.registrations = registrations; this.inputs = inputs; this.environment = environment;
            Ids = ids;
            FileMapScope = fileMapScope;
            MarkdownScope = markdownScope;
            invocation = $"{RootPath}/check-material/{build.Candidate}/{build.Round}/{Guid.NewGuid():N}";
            reused = ImportCheckSeed(root, stage, registration, inputs, output);
        }
        internal bool IsSelected(string id)
        {
            if (!Ids.Contains(id, StringComparer.Ordinal)) return false;
            // Selection happens after describe. A newly produced capability can
            // differ even when its registered source inputs have not changed.
            if (reused.TryGetValue(id, out var previous) && UsesScribe(registrations.Single(check => check.Id == id))
                && completed.TryGetValue("scribe-describe", out var describe) && !SameScribeMaterial(root, previous, describe))
                reused.Remove(id);
            return !reused.ContainsKey(id);
        }
        internal CurrentRuleSelection SelectCurrentRules() => CurrentRuleSelection.Create(
            registrations.Select(check => check.Id).Where(id => id.StartsWith("SL-", StringComparison.Ordinal)).ToArray(),
            Ids.Where(id => id.StartsWith("SL-", StringComparison.Ordinal) && IsSelected(id)).ToArray());

        internal CheckUnitResult Run(string id, Func<CheckWork> execute)
        {
            if (!Ids.Contains(id, StringComparer.Ordinal) || completed.ContainsKey(id))
                throw new InvalidDataException("unregistered or duplicate common execution: " + id);
            var needsScribe = UsesScribe(registrations.Single(check => check.Id == id));
            var describe = needsScribe ? completed.GetValueOrDefault("scribe-describe")
                ?? throw new InvalidDataException("predicate requires completed Scribe producer: " + id) : null;
            if (!IsSelected(id) && reused.TryGetValue(id, out var previous))
            {
                completed.Add(id, previous);
                return previous;
            }
            // A selected callback or malformed current result is fatal. There is no seed
            // fallback after this point, and original files are never rewritten as current.
            var work = execute();
            if (work.Operations is null) throw new InvalidDataException("missing current operations: " + id);
            // Retain the exact capability used by this original predicate, using
            // its existing data/material fields and original execution provenance.
            if (describe is not null)
                work = work with { Data = File.ReadAllText(Path.Combine(root, describe.Data!)) };
            var directory = invocation + "/" + id;
            var operations = work.Operations.Select((operation, index) =>
            {
                var path = directory + "/" + index + ".log";
                Directory.CreateDirectory(Path.Combine(root, directory));
                File.WriteAllText(Path.Combine(root, path), operation.Output);
                var exit = stage == "current" ? CommonStages.Normalize(operation.RawExit) : 0;
                return new StageStep(operation.Name, operation.RawExit, exit, exit == 0 ? "executed" : "failed", path);
            }).ToArray();
            for (var index = 0; index < operations.Length; index++)
                if (operations[index].Exit != 0)
                    throw new CommonCheckFailure(operations[index], work.Operations[index].Output);
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
                foreach (var path in ProducedReportPaths(root))
                {
                    var target = Path.Combine(root, report + path[ReportPath.Length..]);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    if (!File.Exists(target)) File.Copy(Path.Combine(root, path), target);
                }
            }
            var materials = Materials(root, operations.Select(operation => operation.Log)
                .Concat(data is null ? [] : new[] { data })
                .Concat(report is null ? [] : ProducedReportPaths(root).Select(path => report + path[ReportPath.Length..])));
            var unit = new CheckUnitResult(id, inputs[id], "executed", id == "selftest-pair" ? "equal" : "passed", build.Candidate, build.Round, environment, operations, data, report, materials);
            ValidateCheckUnit(root, root, snapshot, unit, inputs[id], build.Candidate, build.Round,
                registration.Fresh(successfulReport));
            completed.Add(id, unit);
            return unit;
        }
        internal RuleExecutionOutcome ExecuteCurrentPredicates(ValidatedPolicy policy, AcceptedLeanClosure? lean)
        {
            if (stage != "current") throw new InvalidDataException("current selection requires current owner");
            if (lean is null && registrations.Any(check => Ids.Contains(check.Id) && check.ReportInputs.Length != 0))
                throw new InvalidDataException("selected current checks require Lean report evidence");
            var verified = completed.TryGetValue("scribe-describe", out var describe) ? ReadScribe(root, describe, snapshot)
                : registrations.Any(check => Ids.Contains(check.Id) && UsesScribe(check))
                    ? throw new InvalidDataException("current predicates require the completed Scribe producer") : VerifiedScribeEmissions.Empty;
            var selection = SelectCurrentRules();
            var context = lean is null ? CurrentRuleContext.CreateWithoutLean(snapshot, policy, verified, selection)
                : CurrentRuleContext.Create(snapshot, policy, lean, verified, selection);
            var evaluated = AdmissionPipeline.CheckCurrent(context);
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
                catch (CommonCheckFailure) when (diagnostics.Any(d => d.AdmissionEffect != AdmissionEffect.Observe)) { failed.Add(id); }
            }
            var diagnosticsCombined = PredicateDiagnostics(root, completed.Values).AddRange(actual.Diagnostics.Where(d => failed.Contains(d.RuleId.Value)
                || d.RuleId.Value == "SL-000" && failed.Contains("SL-015")));
            return new RuleExecutionOutcome.Completed(CompletedRuleSet.Create(
                diagnosticsCombined.OrderBy(d => d.RuleId.Value, StringComparer.Ordinal).ThenBy(d => d.Path, StringComparer.Ordinal)
                    .ThenBy(d => d.Message, StringComparer.Ordinal).ToImmutableArray(),
                actual.DeferredRules, actual.ExecutedRules, actual.SkippedRules));
        }

        internal CommonCheckRecord Seal() => Seal(null);

        internal void SealEngineering(StageStep[] steps)
        {
            if (stage != "engineering") throw new InvalidDataException("engineering seal requires engineering checks");
            // All callbacks have finished. These consecutive seals observe one
            // fresh source snapshot; writing the check receipt starts a new
            // material-hash scope before that receipt is validated and bound.
            var validation = ValidationScope.Create(root);
            _ = Seal(validation);
            CommonExecutionEvidence.SealEngineering(root, build, steps, validation.Fresh());
        }

        private CommonCheckRecord Seal(ValidationScope? validation)
        {
            var record = new CommonCheckRecord(2, stage, build.Candidate, build.Round,
                Ids.Select(id => completed.TryGetValue(id, out var unit) ? unit
                    : throw new InvalidDataException("required common unit did not run: " + id)).ToArray());
            ValidateStartedBuild(root, build, validation is null ? Candidate(root) : Candidate(root, validation.Snapshot), validation);
            ValidateCheckRecord(root, record, validation?.Snapshot ?? snapshot, inputs, build.Candidate, build.Round, Ids,
                validation ?? registration.Fresh());
            Write(root, ChecksPath(stage), record);
            return record;
        }
    }

    internal static CommonCheckRecord ValidateChecks(string root, string stage, CommonStageRecord build, string[]? selectedIds = null)
        => ValidateChecks(root, stage, build, selectedIds, ValidationScope.Create(root));

    private static CommonCheckRecord ValidateChecks(string root, string stage, CommonStageRecord build, string[]? selectedIds, ValidationScope validation)
    {
        var record = Read<CommonCheckRecord>(root, ChecksPath(stage));
        if (record.Stage != stage) throw new InvalidDataException("common check stage mismatch");
        var snapshot = validation.Snapshot;
        var ids = selectedIds ?? CheckIds(stage, validation.CheckManifest());
        // Transport validates the retained execution. Local reuse separately requires
        // this consumer's environment, including OS/architecture binary isolation.
        ValidateCheckRecord(root, record, snapshot, null, build.Candidate, build.Round, ids, validation,
            stage == "current" ? CurrentPlan(root, build)?.ChangedPaths : null);
        return record;
    }
    private static void ValidateCheckRecord(string root, CommonCheckRecord record, RepositorySnapshot snapshot,
        IReadOnlyDictionary<string, string>? inputs, string candidate, string round, string[] expected, ValidationScope? validation = null,
        IReadOnlyCollection<string>? changedPaths = null)
    {
        validation ??= new ValidationScope(snapshot);
        if (record.Version != 2 || !ValidCandidate(record.Candidate) || !ValidRound(record.Round) || record.Candidate != candidate || record.Round != round || record.Units is null || record.Units.Any(unit => unit is null))
            throw new InvalidDataException("common check candidate or round mismatch");
        if (!expected.SequenceEqual(record.Units.Select(unit => unit.Id)))
            throw new InvalidDataException("missing, duplicated or unordered common check result");
        var originalInputs = new Dictionary<string, IReadOnlyDictionary<string, string>>(StringComparer.Ordinal);
        foreach (var unit in record.Units)
        {
            ValidateExecutionEnvironment(root, unit.ExecutionEnvironment);
            if (inputs is null && !originalInputs.ContainsKey(unit.ExecutionEnvironment))
                originalInputs.Add(unit.ExecutionEnvironment, CheckInputFingerprints(root, snapshot, currentReport: record.Stage == "current",
                    selectedIds: expected, executionEnvironment: unit.ExecutionEnvironment, validation: validation, changedPaths: changedPaths));
            ValidateCheckUnit(root, root, snapshot, unit, (inputs ?? originalInputs[unit.ExecutionEnvironment])[unit.Id], candidate, round, validation);
        }
        foreach (var check in validation.CheckManifest().Where(check => expected.Contains(check.Id) && UsesScribe(check)))
            if (record.Stage == "current" && !SameScribeMaterial(root, record.Units.Single(unit => unit.Id == check.Id),
                record.Units.Single(unit => unit.Id == "scribe-describe")))
                throw new InvalidDataException("predicate Scribe material differs from current producer: " + check.Id);
    }
    private static void ValidateCheckUnit(string materialRoot, string sourceRoot, RepositorySnapshot snapshot,
        CheckUnitResult unit, string fingerprint, string candidate, string round, ValidationScope? validation = null)
    {
        validation ??= new ValidationScope(snapshot);
        ValidateExecutionEnvironment(sourceRoot, unit.ExecutionEnvironment);
        if (unit.Operations is null || unit.Materials is null || unit.Operations.Any(operation => operation is null || operation.Log is null)
            || unit.Materials.Any(material => material is null || material.Path is null))
            throw new InvalidDataException("missing common unit materials: " + unit.Id);
        var registration = validation.CheckManifest().Single(check => check.Id == unit.Id);
        if ((registration.ReportInputs.Length != 0) != (unit.Report is not null))
            throw new InvalidDataException("common report declaration/material mismatch: " + unit.Id);
        ValidateCheckProvenance(unit, candidate, round);
        if (unit.Result != (unit.Id == "selftest-pair" ? "equal" : "passed") || unit.InputFingerprint != fingerprint)
            throw new InvalidDataException("invalid common check identity/provenance: " + unit.Id);
        var prefix = $"{RootPath}/check-material/{unit.ExecutionCandidate}/{unit.ExecutionRound}/";
        var required = unit.Operations.Select(operation => operation.Log).Concat(unit.Data is null ? [] : new[] { unit.Data })
            .Concat(unit.Report is null ? [] : ReportPaths.Select(path => unit.Report + path[ReportPath.Length..]))
            .Concat(unit.Report is not null && unit.Materials.Any(material => material.Path == unit.Report + ReportReuseSuffix)
                ? [unit.Report + ReportReuseSuffix] : []).Order(StringComparer.Ordinal).ToArray();
        if (required.Length == 0 || required.Distinct(StringComparer.Ordinal).Count() != required.Length
            || !required.SequenceEqual(unit.Materials.Select(material => material.Path).Order(StringComparer.Ordinal))
            || required.Any(path => !path.StartsWith(prefix, StringComparison.Ordinal)))
            throw new InvalidDataException("missing or contradictory common material: " + unit.Id);
        ValidateMaterials(materialRoot, unit.Materials, validation);
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
            validation.Report(Path.Combine(materialRoot, unit.Report));
            if (validation.Hash(Path.Combine(materialRoot, unit.Report)) != validation.Hash(Path.Combine(sourceRoot, ReportPath)))
                throw new InvalidDataException("original common report differs from current validated report: " + unit.Id);
        }
        if (unit.Id.StartsWith("SL-", StringComparison.Ordinal)) _ = ReadPredicate(materialRoot, unit);
        if (unit.Id == "scribe-describe") _ = ReadScribe(materialRoot, unit, snapshot);
        if (UsesScribe(registration))
        {
            if (unit.Data is null) throw new InvalidDataException("missing predicate Scribe material: " + unit.Id);
            _ = VerifiedScribeEmissions.ReadMaterial(File.ReadAllText(Path.Combine(materialRoot, unit.Data)), snapshot);
        }
    }

    private static void ValidateCheckProvenance(CheckUnitResult unit, string candidate, string round)
    {
        if (unit.Status is not ("executed" or "reused") || !ValidCandidate(unit.ExecutionCandidate) || !ValidRound(unit.ExecutionRound)
            || unit.Status == "executed" && (unit.ExecutionCandidate != candidate || unit.ExecutionRound != round))
            throw new InvalidDataException("invalid common check identity/provenance: " + unit.Id);
    }

    private static bool SameScribeMaterial(string root, CheckUnitResult predicate, CheckUnitResult describe) =>
        predicate.Data is not null && describe.Data is not null
        && Hash(Path.Combine(root, predicate.Data)) == Hash(Path.Combine(root, describe.Data));

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
