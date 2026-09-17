using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum InformationTemplateBindingState
{
    Undeclared,
    DeclaredUnresolved,
    DeclaredValidated,
}

internal sealed record InformationTemplateOccurrence(
    InformationOccurrenceKey Key,
    string RegistrationSourcePath,
    string StatementIdentity,
    ImmutableArray<InformationTemplateContentInput> ContentInputs,
    InformationTemplateBindingState State,
    string? EvidenceRef,
    string? Diagnostic,
    string? BindingSourcePath,
    string? UnitName = null,
    string? RealizationName = null);

internal sealed record InformationTemplateUniverse(
    ImmutableDictionary<InformationOccurrenceKey, InformationTemplateOccurrence> Occurrences,
    ImmutableHashSet<InformationOccurrenceKey> Inventory,
    ImmutableHashSet<string> GovernedSources,
    ImmutableHashSet<string> AssessedSources);

internal sealed record DeclaredTemplateFinding(string Code, string Path, string Detail);

// The core consumes independently reconciled, source-bound evidence. Its domain
// observer is output-only: it cannot alter any predicate or supply an admission.
internal static class DeclaredTemplateBindingRule
{
    internal static bool IsAffectedBy(RuleEvaluationContext context) =>
        (context.Baseline.TryGetFile(InformationTemplateDebtStore.ActivationPath, out _)
            || context.Current.TryGetFile(InformationTemplateDebtStore.ActivationPath, out _))
        && (context.RuleImplementationChanged || context.Changes.Paths.Any(path =>
            path.Value.StartsWith("D5/", StringComparison.Ordinal)
            || path.Value.StartsWith(InformationTemplateDebtStore.Root, StringComparison.Ordinal)
            || path.Value.StartsWith("Golden/Frozen/state/", StringComparison.Ordinal)
            || path.Value == AdmissionPlanePolicy.FileMapPath));

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        if (!IsAffectedBy(context)) return [];
        try
        {
            var baseline = context.Baseline;
            var candidate = context.Current;
            if (!baseline.TryGetFile(InformationTemplateDebtStore.ActivationPath, out _))
            {
                // Installation validates candidate data but does not take it as
                // effective authority. It takes effect only in a future protected base.
                var installation = InformationTemplateDebtStore.ReadActivation(candidate);
                if (installation.Activated || HasRows(candidate))
                    throw new FormatException("DTR-Activation: installation must be inactive and row-free");
                return [new(InformationTemplateDebtStore.ActivationPath,
                    "DTR-Inactive installation; protected activation is absent", AdmissionEffect.Observe)];
            }
            var activation = InformationTemplateDebtStore.ReadActivation(baseline);
            if (!candidate.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var candidateActivation))
                return [new(InformationTemplateDebtStore.ActivationPath, "DTR-Required activation mechanism deleted")];
            var changed = context.Changes.Paths.Select(path => path.Value).ToHashSet(StringComparer.Ordinal);
            CheckRouting(baseline, candidate, changed);
            var after = InformationTemplateEvidence.Collect(candidate, context.Lean.Report);
            if (!activation.Activated && !HasRows(baseline) && !HasRows(candidate)
                && !InformationTemplateDebtStore.ReadActivation(candidate).Activated)
            {
                var canonicalInactive = InformationTemplateDebtStore.WriteActivation(activation);
                if (!candidateActivation.RawBytes.AsSpan().SequenceEqual(canonicalInactive.AsSpan()))
                    throw new FormatException("DTR-Activation: seeding must precede activation");
                if (after.Occurrences.Values.Any(o => o.State != InformationTemplateBindingState.Undeclared))
                    throw new FormatException("DTR-Activation: declarations precede activation");
                return [new(InformationTemplateDebtStore.ActivationPath,
                    "DTR-Inactive complete producer; seed-only writer available", AdmissionEffect.Observe)];
            }
            var evidence = context.Lean.Report.TemplateEvidenceContext
                ?? throw new FormatException("DTR-Evidence: historical evidence reader unavailable");
            var seed = evidence.ReadHistorical(activation.SeedBase);
            var seedUniverse = InformationTemplateEvidence.Collect(
                InformationTemplateEvidence.HistoricalInputs(seed.Snapshot, candidate), seed.Report);
            var protectedEvidence = evidence.ReadHistorical(evidence.ProtectedRevision);
            var before = InformationTemplateEvidence.Collect(
                InformationTemplateEvidence.HistoricalInputs(baseline, candidate), protectedEvidence.Report);
            var baseDebt = InformationTemplateDebtStore.Load(baseline, activation, seed.Snapshot);
            var headDebt = InformationTemplateDebtStore.Load(candidate, activation, seed.Snapshot);
            if (!activation.Activated)
                CheckSeed(activation, seed.Snapshot, seedUniverse, headDebt);
            var findings = Evaluate(activation, baseline, candidate, baseDebt, headDebt,
                before, after, changed).Select(f => new RuleFinding(f.Path, f.Code + " " + f.Detail)).ToImmutableArray();
            return findings.Add(new(InformationTemplateDebtStore.ActivationPath,
                activation.Activated ? "DTR-Domain completed declared-template consumer"
                    : "DTR-Inactive seed relation checked", AdmissionEffect.Observe));
        }
        catch (Exception error) when (error is FormatException or IOException or InvalidOperationException)
        {
            return [new(InformationTemplateDebtStore.ActivationPath, "DTR-Evidence " + error.Message)];
        }
    }

    internal static void CheckSeed(InformationTemplateActivation activation, RepositorySnapshot seed,
        InformationTemplateUniverse universe,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> rows)
    {
        if (!universe.Inventory.SetEquals(universe.Occurrences.Keys)
            || !universe.GovernedSources.SetEquals(universe.AssessedSources)
            || !universe.Inventory.SetEquals(rows.Keys))
            throw new FormatException("DTR-Seed: seed rows differ from complete original occurrence inventory");
        foreach (var (key, occurrence) in universe.Occurrences)
        {
            if (occurrence.State != InformationTemplateBindingState.Undeclared
                || !seed.TryGetFile(occurrence.RegistrationSourcePath, out var source))
                throw new FormatException("DTR-Seed: original occurrence/source unavailable or already declared");
            var expected = new InformationTemplateDebtRow(key, activation.SeedBase, occurrence.StatementIdentity,
                InformationTemplateJson.Sha256(source.RawBytes.AsSpan()), occurrence.ContentInputs);
            if (!InformationTemplateDebtStore.WriteRow(expected).AsSpan().SequenceEqual(
                InformationTemplateDebtStore.WriteRow(rows[key]).AsSpan()))
                throw new FormatException("DTR-Seed: row does not bind original statement/source/content inputs");
        }
    }

    internal static bool HasRows(RepositorySnapshot snapshot) => snapshot.Files.Keys.Any(path =>
        path.Value.StartsWith(InformationTemplateDebtStore.Root, StringComparison.Ordinal)
        && path.Value != InformationTemplateDebtStore.ActivationPath);

    internal static void CheckRouting(RepositorySnapshot baseline, RepositorySnapshot candidate,
        IReadOnlySet<string> changed)
    {
        var content = changed.Where(path => path.StartsWith("D5/", StringComparison.Ordinal)
            || path.StartsWith(InformationTemplateDebtStore.Root, StringComparison.Ordinal)
                && path != InformationTemplateDebtStore.ActivationPath).ToArray();
        if (content.Length == 0) return;
        if (!baseline.TryGetFile(AdmissionPlanePolicy.FileMapPath, out _)
            || !candidate.TryGetFile(AdmissionPlanePolicy.FileMapPath, out _))
            throw new FormatException("DTR-Routing: protected/candidate FILEMAP unavailable");
        static RawRepositorySnapshot PolicySnapshot(RepositorySnapshot snapshot) =>
            RawRepositorySnapshot.Create(snapshot.Files.Values
                .Where(file => FileMapDocuments.IsPolicyPath(file.Path.Value))
                .Select(file => new RawRepositoryEntry(file.Path.Value, file.RawBytes)));
        var oldPolicy = PolicySnapshot(baseline);
        var newPolicy = PolicySnapshot(candidate);
        var delta = RawChangeSet.Create(changed);
        var baseDelta = AdmissionPlanePolicy.Evaluate(oldPolicy, oldPolicy, delta);
        var headDelta = AdmissionPlanePolicy.Evaluate(newPolicy, newPolicy, delta);
        if (!baseDelta.IsAdmissible || !headDelta.IsAdmissible
            || baseDelta.Classification != AdmissionPlaneClassification.ContentOnly
            || headDelta.Classification != baseDelta.Classification)
            throw new FormatException("DTR-Routing: mixed delta or base/candidate partition differs");
        var contentDelta = RawChangeSet.Create(content);
        var before = AdmissionPlanePolicy.Evaluate(oldPolicy, oldPolicy, contentDelta);
        var after = AdmissionPlanePolicy.Evaluate(newPolicy, newPolicy, contentDelta);
        if (!before.IsAdmissible || !after.IsAdmissible
            || before.Classification != AdmissionPlaneClassification.ContentOnly
            || after.Classification != before.Classification)
            throw new FormatException("DTR-Routing: base/candidate content classification differs");
    }

    internal static ImmutableArray<DeclaredTemplateFinding> Evaluate(
        InformationTemplateActivation activation,
        RepositorySnapshot baseline,
        RepositorySnapshot candidate,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> baseDebt,
        ImmutableDictionary<InformationOccurrenceKey, InformationTemplateDebtRow> headDebt,
        InformationTemplateUniverse before,
        InformationTemplateUniverse after,
        IReadOnlySet<string> changedPaths,
        Action<InformationOccurrenceKey>? observedInvocation = null)
    {
        var findings = ImmutableArray.CreateBuilder<DeclaredTemplateFinding>();
        void Add(string code, string detail, string? path = null) => findings.Add(new(
            code, path ?? InformationTemplateDebtStore.ActivationPath, detail));

        if (!candidate.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var candidateActivation)
            || !baseline.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var baseActivation))
        {
            Add("DTR-Required", "protected activation mechanism is missing");
            return findings.ToImmutable();
        }

        // Candidate bytes are never the effective activation input. The only
        // permitted transition is to the active encoding of the protected seed.
        if (!candidateActivation.RawBytes.AsSpan().SequenceEqual(baseActivation.RawBytes.AsSpan())
            && (activation.Activated || !candidateActivation.RawBytes.AsSpan().SequenceEqual(
                InformationTemplateDebtStore.WriteActivation(activation with { Activated = true }).AsSpan())))
            Add("DTR-Activation", "seed retargeting, deactivation or noncanonical activation change");

        CheckInventory(before, "base", Add);
        CheckInventory(after, "candidate", Add);
        foreach (var row in baseDebt.Values.Concat(headDebt.Values))
            if (row.SeedBase != activation.SeedBase) Add("DTR-Seed", "row differs from protected seed_base");

        if (!activation.Activated)
        {
            // Inactive installation and seed-only changes cannot start migration.
            foreach (var occurrence in after.Occurrences.Values)
                if (occurrence.State != InformationTemplateBindingState.Undeclared
                    && (!before.Occurrences.TryGetValue(occurrence.Key, out var old)
                        || old != occurrence))
                    Add("DTR-Activation", "declaration migration precedes activation", occurrence.RegistrationSourcePath);
            if (baseDebt.Count > 0 && !baseDebt.Keys.ToHashSet().SetEquals(headDebt.Keys))
                Add("DTR-Activation", "seed-only phase cannot discharge or replace debt");
            return findings.ToImmutable();
        }

        // Set inclusion, not cardinality. A same-sized replacement is new debt.
        if (headDebt.Keys.Any(key => !baseDebt.ContainsKey(key)))
            Add("DTR-Subset", "candidate debt is not a subset of protected debt");
        foreach (var (key, row) in headDebt)
            if (baseDebt.TryGetValue(key, out var old)
                && !InformationTemplateDebtStore.WriteRow(row).AsSpan().SequenceEqual(
                    InformationTemplateDebtStore.WriteRow(old).AsSpan()))
                Add("DTR-Subset", "surviving debt row changed", InformationTemplateDebtStore.PathFor(key));

        foreach (var key in before.Inventory)
            if (!after.Inventory.Contains(key))
                Add("DTR-Inventory", "removing an occurrence does not discharge its enduring obligation",
                    InformationTemplateDebtStore.PathFor(key));

        var undeclared = after.Occurrences.Values.Where(o => o.State == InformationTemplateBindingState.Undeclared)
            .Select(o => o.Key).ToHashSet();
        if (!undeclared.SetEquals(headDebt.Keys))
            Add("DTR-Residual", "debt differs from independently collected undeclared occurrences");

        var touched = baseDebt.Values.Where(row => IsTouched(row, baseline, candidate, changedPaths,
                before.Occurrences.GetValueOrDefault(row.Key), after.Occurrences.GetValueOrDefault(row.Key)))
            .Select(row => row.Key).ToHashSet();
        if (touched.Overlaps(headDebt.Keys) || touched.Count > 0 && headDebt.Count >= baseDebt.Count)
            Add("DTR-Touched", "every touched debt occurrence must discharge and the debt set must strictly shrink");

        foreach (var occurrence in after.Occurrences.Values)
        {
            if (!before.Inventory.Contains(occurrence.Key)
                && occurrence.State != InformationTemplateBindingState.DeclaredValidated)
                Add("DTR-New", "candidate-new occurrence requires validated declaration", occurrence.RegistrationSourcePath);
            if (occurrence.State == InformationTemplateBindingState.DeclaredUnresolved)
                Add("DTR-Evidence", occurrence.Diagnostic ?? "declared occurrence is unresolved", occurrence.RegistrationSourcePath);
        }

        var firstFreezeSources = changedPaths.Where(path => !baseline.TryGetFile(path, out _))
            .Select(path => FrozenStatePath.TryToModulePath(path, out var module) ? module.Value : null)
            .Where(path => path is not null).ToHashSet(StringComparer.Ordinal);
        var delta = after.Occurrences.Values.Where(o => !before.Inventory.Contains(o.Key)
                || touched.Contains(o.Key) || firstFreezeSources.Contains(o.RegistrationSourcePath)
                || o.ContentInputs.Any(i => changedPaths.Contains(i.Path) || firstFreezeSources.Contains(i.Path))
                || o.BindingSourcePath is { } binding && changedPaths.Contains(binding))
            .Select(o => o.Key).ToImmutableHashSet();
        foreach (var key in SelectDomain(headDebt.Count, after.Inventory, delta))
        {
            observedInvocation?.Invoke(key);
            if (!after.Occurrences.TryGetValue(key, out var occurrence)
                || occurrence.State != InformationTemplateBindingState.DeclaredValidated
                || occurrence.EvidenceRef is null)
                Add("DTR-Evidence", "selected occurrence lacks a source-bound certificate",
                    InformationTemplateDebtStore.PathFor(key));
        }

        return findings.ToImmutable();
    }

    internal static ImmutableHashSet<InformationOccurrenceKey> SelectDomain(int residualCount,
        ImmutableHashSet<InformationOccurrenceKey> universe, ImmutableHashSet<InformationOccurrenceKey> delta) =>
        residualCount == 0 ? universe : delta;

    private static void CheckInventory(InformationTemplateUniverse value, string side,
        Action<string, string, string?> add)
    {
        if (!value.Inventory.SetEquals(value.Occurrences.Keys)
            || !value.GovernedSources.SetEquals(value.AssessedSources))
            add("DTR-Inventory", side + " inventory/registry/source coverage mismatch", null);
    }

    private static bool IsTouched(InformationTemplateDebtRow row, RepositorySnapshot baseline,
        RepositorySnapshot candidate, IReadOnlySet<string> changed,
        InformationTemplateOccurrence? before, InformationTemplateOccurrence? after)
    {
        if (before is null || after is null || before.StatementIdentity != after.StatementIdentity
            || before.State != after.State || before.BindingSourcePath != after.BindingSourcePath)
            return true;
        if (after.BindingSourcePath is { } binding && changed.Contains(binding)) return true;
        foreach (var path in changed)
            if (!baseline.TryGetFile(path, out _) && FrozenStatePath.TryToModulePath(path, out var module)
                && (module.Value == after.RegistrationSourcePath
                    || row.ContentInputs.Any(input => input.Path == module.Value)
                    || before.ContentInputs.Any(input => input.Path == module.Value)
                    || after.ContentInputs.Any(input => input.Path == module.Value))) return true;
        // Judge/compiler/toolchain files do not enter the producer's content slice.
        return row.ContentInputs.Any(input =>
            !baseline.TryGetFile(input.Path, out var old) || !candidate.TryGetFile(input.Path, out var current)
            || !old.RawBytes.AsSpan().SequenceEqual(current.RawBytes.AsSpan()));
    }
}
