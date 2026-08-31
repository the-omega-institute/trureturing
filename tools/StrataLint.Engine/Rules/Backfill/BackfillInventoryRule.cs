using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record BackfillInventoryValidationContext(
    RepositorySnapshot Current,
    RepositorySnapshot Baseline,
    ValidatedPolicy Policy,
    AcceptedLeanClosure? Lean,
    VerifiedScribeEmissions? VerifiedScribeEmissions,
    RawChangeSet? Changes = null,
    Func<string, bool>? IsBaseFactAffected = null,
    RawChangeSet? RepositoryChanges = null,
    RawChangeSet? CasChanges = null,
    RawChangeSet? ProjectedStatusChanges = null);

internal static class BackfillInventoryRule
{
    private const string BackfillPath = BackfillInventoryLoader.RelativePath;

    private static readonly Regex SourceIdPattern = new(
        "^[a-z0-9]+(?:[.-][a-z0-9]+)*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex AtomIdPattern = new(
        "^[A-Za-z0-9]+(?:[.-][A-Za-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
        => Evaluate(context, changes: null);

    internal static ImmutableArray<RuleFinding> EvaluateCandidateDelta(RuleEvaluationContext context)
        => Evaluate(context, context.Changes);

    internal static bool IsAffectedBy(RuleEvaluationContext context)
    {
        foreach (var path in context.Changes.Paths)
        {
            if (BackfillInventoryLoader.IsCanonicalPath(path.Value)
                || DigestionCasStore.IsCanonicalPath(path.Value)
                || path.Value == BackfillInventoryLoader.RelativePath
                || path.Value == TheoryAtomizerDataLoader.DataPath
                || DigestionLedgerAligner.IsAtomizerImplementationPath(path.Value)
                || path.Value is "Meta/registry.yaml" or "Meta/domains.yaml"
                || FrozenLedgerDeltaPredicate.IsEnvironmentInput(path.Value)
                // 理论卷按路径规则治理后,`GovernanceDocuments` 里已无理论路径;
                // 若此处仍只靠那张清单,只改理论卷的候选就**整条规则不触发**
                // (RuleCatalog 对未命中的规则整条跳过),消化账本检测随之失效。
                // 实测见 #2462:追加一条可原子化命题、不跑 make ingest,gate EXIT=0。
                || DigestionOpaquePathPolicy.IsTheoryDocument(path)
                || context.Policy.GovernanceDocuments.Contains(path))
            {
                return true;
            }
        }

        if (context.RuleImplementationChanged)
        {
            return true;
        }

        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        return BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            document,
            context.Changes).HasAffectedEdges;
    }

    private static ImmutableArray<RuleFinding> Evaluate(
        RuleEvaluationContext context,
        RawChangeSet? changes)
    {
        BackfillInventoryDocument document;
        RawChangeSet? evaluationChanges = changes;
        RawChangeSet? receiptVerificationChanges = changes;
        Func<string, bool>? isBaseFactAffected = null;
        try
        {
            document = changes is null
                ? BackfillInventoryLoader.Load(context.Current)
                : BackfillInventoryLoader.LoadCandidateDelta(
                    context.Current,
                    context.Baseline,
                    changes);
            if (changes is not null)
            {
                var impact = BackfillDeltaImpactResolver.Resolve(
                    context.Current,
                    context.Baseline,
                    document,
                    changes);
                evaluationChanges = impact.EvaluationChanges;
                receiptVerificationChanges = impact.ReceiptVerificationChanges;
                var affectedPaths = evaluationChanges.Paths
                    .Select(static path => path.Value)
                    .ToHashSet(StringComparer.Ordinal);
                isBaseFactAffected = affectedPaths.Contains;
                document = BackfillInventoryLoader.LoadCandidateDelta(
                    context.Current,
                    context.Baseline,
                    evaluationChanges);
            }
        }
        catch (FormatException exception)
        {
            return [new RuleFinding(BackfillPath, exception.Message)];
        }

        return EvaluateDocument(
            new BackfillInventoryValidationContext(
                context.Current,
                context.ForkPoint,
                context.Policy,
                context.Lean,
                context.VerifiedScribeEmissions,
                receiptVerificationChanges,
                isBaseFactAffected,
                RepositoryChanges: changes,
                ProjectedStatusChanges: evaluationChanges),
            document);
    }

    internal static ImmutableArray<RuleFinding> EvaluateDocument(
        BackfillInventoryValidationContext context,
        BackfillInventoryDocument document) =>
        EvaluateDocument(context, document, validateTruthAlignment: true);

    internal static ImmutableArray<RuleFinding> EvaluateDocumentWithoutTruthAlignment(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        BackfillInventoryDocument document,
        RawChangeSet? changes = null,
        Func<string, bool>? isBaseFactAffected = null,
        RawChangeSet? repositoryChanges = null,
        RawChangeSet? casChanges = null) =>
        EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                baseline,
                policy,
                Lean: null,
                VerifiedScribeEmissions: null,
                changes,
                isBaseFactAffected,
                repositoryChanges,
                casChanges),
            document,
            validateTruthAlignment: false);

    private static ImmutableArray<RuleFinding> EvaluateDocument(
        BackfillInventoryValidationContext context,
        BackfillInventoryDocument document,
        bool validateTruthAlignment)
    {
        ArgumentNullException.ThrowIfNull(context);
        ArgumentNullException.ThrowIfNull(document);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var finding in DigestionCasStore.ValidateAppendOnly(
                     context.Current,
                     context.Baseline,
                     context.RepositoryChanges ?? context.Changes))
        {
            findings.Add(new RuleFinding(BackfillPath, finding));
        }

        var root = document.Root;
        if (!root.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                ["schema_version", "ledger", "sources"]))
        {
            findings.Add(new RuleFinding(BackfillPath, "BACKFILL top-level keys are not canonical"));
        }

        ImmutableArray<DigestionLedgerSource> sources;
        try
        {
            sources = document.RequireDigestionSources();
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(BackfillPath, exception.Message));
            sources = default;
        }

        if (!sources.IsDefault)
        {
            ValidateDigestionEntries(
                context,
                document,
                sources,
                sources.SelectMany(static source => source.Entries).ToImmutableArray(),
                findings,
                validateTruthAlignment);
        }

        return findings.ToImmutable();
    }

    /// <summary>
    /// The inverse of the source-path check above, and the reason it exists: that one asks
    /// whether a declared source names a governed document, this one asks whether a
    /// governed theory document has a source. Without it a volume can sit in the tree
    /// undigested with nothing red — a dangling reference in the direction nobody checks,
    /// which produces no symptom because the thing that is missing is the reader.
    /// </summary>
    private static void ValidateTheoryCoverage(
        BackfillInventoryValidationContext context,
        IEnumerable<string> declaredPaths,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        // 扫**文件树**,不扫 registry 清单。理论卷已改为按路径规则治理,不再逐个枚举进
        // governance_documents;若这里仍遍历那张清单,清单一空本检查就静默失效——
        // 那正是「新增 markdown 无人过问」的旧病换了个方向复发。
        var declared = declaredPaths.ToHashSet(StringComparer.Ordinal);
        foreach (var path in context.Current.Files.Keys
                     .Select(static path => path.Value)
                     .Where(static path => path.StartsWith(
                         DigestionOpaquePathPolicy.TheoryRootPath,
                         StringComparison.Ordinal))
                     .Where(path => !declared.Contains(path))
                     .Order(StringComparer.Ordinal))
        {
            // 与「未登记残余原子」同理:全新理论卷入库但尚未跑 ingest,是账本四态里的
            // `open`,不是违规。一个只改 markdown 的 PR 不该被它挡住——第三方本来就
            // 跑不了本仓的 producer。判词照发(带补救命令),但不阻断准入。
            findings.Add(new RuleFinding(
                BackfillPath,
                $"theory document '{path}' has no digestion source: run make ingest, "
                + "which registers it with the default atomizer",
                AdmissionEffect.Observe));
        }
    }

    private static void ValidateDigestionEntries(
        BackfillInventoryValidationContext context,
        BackfillInventoryDocument document,
        ImmutableArray<DigestionLedgerSource> sources,
        ImmutableArray<DigestionLedgerEntry> entries,
        ImmutableArray<RuleFinding>.Builder findings,
        bool validateTruthAlignment)
    {
        if (sources.Length == 0)
        {
            findings.Add(new RuleFinding(BackfillPath, "digestion ledger must contain at least one source"));
            return;
        }

        var seenSourceIds = new HashSet<string>(StringComparer.Ordinal);
        var changedSourceIds = new HashSet<string>(StringComparer.Ordinal);
        var seenPaths = new Dictionary<string, string>(StringComparer.Ordinal);
        var changedPaths = new HashSet<string>(StringComparer.Ordinal);
        var validateAllRecords = context.Changes is null;
        foreach (var source in sources)
        {
            var sourceMetadataChanged = validateAllRecords
                || SourceMetadataChanged(source, context.Changes);
            if (sourceMetadataChanged)
            {
                changedSourceIds.Add(source.SourceId);
                changedPaths.Add(source.SourcePath);
            }

            if (!seenSourceIds.Add(source.SourceId))
            {
                if (sourceMetadataChanged || changedSourceIds.Contains(source.SourceId))
                {
                    findings.Add(new RuleFinding(BackfillPath, $"duplicate source_id: {source.SourceId}"));
                }
            }

            if (sourceMetadataChanged && !SourceIdPattern.IsMatch(source.SourceId))
            {
                findings.Add(new RuleFinding(BackfillPath, $"invalid source_id: {source.SourceId}"));
            }

            if (sourceMetadataChanged && source.Entries.Length == 0)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} must contain at least one atomic entry"));
            }

            // 理论卷按**规则**治理(路径在理论根下),不再逐个枚举进 registry.yaml:
            // 否则第三方 PR 加一个 markdown 就被迫改 harness,而它的名字无法预先枚举
            // (与 docs/reports/ 同性质;CLAUDE.md 商余结构)。其余治理文档仍按清单。
            if (sourceMetadataChanged
                && (!RepoPath.TryCreate(source.SourcePath, out var sourcePath)
                || !(context.Policy.GovernanceDocuments.Contains(sourcePath)
                    || DigestionOpaquePathPolicy.IsTheoryDocument(sourcePath))))
            {
                // First thing a new volume hits, so the verdict carries its own remedy
                // rather than leaving the reader to find which registry field is meant.
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} has an invalid governance path "
                    + $"'{source.SourcePath}': add it to governance_documents in "
                    + "Meta/registry.yaml"));
            }
            else if (sourceMetadataChanged)
            {
                if (source.Atomizer == AtomizerRegistry.NoAtomizerId
                    && !context.Current.TryGetFile(source.SourcePath, out _))
                {
                    findings.Add(new RuleFinding(BackfillPath, $"source path is dangling: {source.SourcePath}"));
                }

                if (Path.GetFileName(source.SourcePath).Contains(' '))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"source filename contains spaces: {source.SourcePath}"));
                }
            }

            if (sourceMetadataChanged
                && source.Atomizer != AtomizerRegistry.NoAtomizerId
                && !AtomizerRegistry.IsRegistered(source.Atomizer))
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"source {source.SourceId} has unknown atomizer {source.Atomizer}. "
                    + "Registered atomizers: "
                    + string.Join(", ", AtomizerRegistry.RegisteredIds)
                    + "."));
            }

            if (seenPaths.TryGetValue(source.SourcePath, out var priorSource))
            {
                if (sourceMetadataChanged || changedPaths.Contains(source.SourcePath))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"duplicate source path: {source.SourcePath} ({priorSource}, {source.SourceId})"));
                }
            }
            else
            {
                seenPaths.Add(source.SourcePath, source.SourceId);
            }
        }

        ValidateTheoryCoverage(context, seenPaths.Keys, findings);

        if (entries.Length == 0)
        {
            return;
        }

        var seenAtomIds = new HashSet<string>(StringComparer.Ordinal);
        var changedAtomIds = new HashSet<string>(StringComparer.Ordinal);
        foreach (var entry in entries)
        {
            var entryChanged = validateAllRecords
                || changedSourceIds.Contains(entry.SourceId)
                || context.Changes is not null
                    && DigestionCasStore.EntryChanged(entry, context.Changes);
            if (entryChanged)
            {
                changedAtomIds.Add(entry.AtomId);
            }

            if (!seenAtomIds.Add(entry.AtomId))
            {
                if (entryChanged || changedAtomIds.Contains(entry.AtomId))
                {
                    findings.Add(new RuleFinding(BackfillPath, $"duplicate atom_id: {entry.AtomId}"));
                }
            }

            if (entryChanged && !AtomIdPattern.IsMatch(entry.AtomId))
            {
                findings.Add(new RuleFinding(BackfillPath, $"invalid atom_id: {entry.AtomId}"));
            }

            if (entryChanged
                && entry.CoverageGids.Distinct(StringComparer.Ordinal).Count() != entry.CoverageGids.Length)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"entry {entry.AtomId} has duplicate coverage GIDs"));
            }

            foreach (var gidText in entry.CoverageGids)
            {
                if (!Gid.TryParse(gidText, out var gid))
                {
                    if (entryChanged)
                    {
                        findings.Add(new RuleFinding(
                            BackfillPath,
                            $"entry {entry.AtomId} has invalid coverage GID {gidText}"));
                    }
                }
                else if (entryChanged && !context.Current.TryGetFile(gid.Path.Value, out _))
                {
                    findings.Add(new RuleFinding(
                        BackfillPath,
                        $"entry {entry.AtomId} coverage target is absent: {gidText}"));
                }
            }
        }

        var hasStructuralFindings = findings.Count > 0;
        // CAS integrity is part of SL-016 itself, so it must run even when another
        // receipt-shape finding below would otherwise return before status derivation.
        // The result is threaded into the alignment pass below, which used to recompute it.
        var casEvaluation = DigestionCasStore.Evaluate(
            document,
            context.Current,
            context.CasChanges ?? context.Changes,
            context.IsBaseFactAffected);
        foreach (var finding in casEvaluation.Findings)
        {
            findings.Add(new RuleFinding(BackfillPath, finding));
        }

        if (!validateTruthAlignment)
        {
            return;
        }

        if (hasStructuralFindings)
        {
            return;
        }

        try
        {
            var baselineDocument = LoadBaselineDocument(context.Baseline);
            foreach (var finding in DigestionFormalizationPrecommitmentValidator.ValidateNewEdges(
                         baselineDocument,
                         document,
                         context.Baseline,
                         context.Lean!.Report))
            {
                findings.Add(new RuleFinding(BackfillPath, finding, AdmissionEffect.Block));
            }

            var evaluation = DigestionStatusEvaluator.Evaluate(
                context.Changes is null
                    ? DigestionEvaluationScope.FullScan
                    : DigestionEvaluationScope.ChangedSet,
                document,
                context.Current,
                context.Lean!,
                context.VerifiedScribeEmissions,
                baselineDocument,
                baselineSnapshot: context.Baseline,
                casEvaluation: casEvaluation,
                changes: context.Changes,
                casChanges: context.CasChanges,
                isBaseFactAffected: context.IsBaseFactAffected,
                projectedStatusChanges: context.ProjectedStatusChanges ?? context.Changes);
            foreach (var finding in evaluation.Findings)
            {
                findings.Add(new RuleFinding(BackfillPath, finding));
            }

            findings.AddRange(ClassifyReceiptIntegrityGaps(evaluation));

            // 观察项不阻断准入。理论卷入库后尚未消化是账本四态里的 `open`,
            // 由本地 `make ingest` 闭合;它不该挡住一个只改 markdown 的 PR。
            foreach (var observation in evaluation.Observations)
            {
                findings.Add(new RuleFinding(BackfillPath, observation, AdmissionEffect.Observe));
            }
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(BackfillPath, exception.Message));
        }
    }

    internal static ImmutableArray<RuleFinding> ClassifyReceiptIntegrityGaps(
        DigestionLedgerEvaluation evaluation)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        return evaluation.ReceiptIntegrityGaps
            .Select(static item => new RuleFinding(
                BackfillPath,
                $"{item.Entry.AtomId}:{item.Gap.Code}:{item.Gap.Detail}",
                AdmissionEffect.Block))
            .ToImmutableArray();
    }

    private static BackfillInventoryDocument LoadBaselineDocument(RepositorySnapshot baseline)
    {
        try
        {
            return BackfillInventoryLoader.LoadBaseline(baseline);
        }
        catch (FormatException exception) when (
            string.Equals(exception.Message, "required governance document is missing", StringComparison.Ordinal))
        {
            throw new FormatException("baseline digestion ledger is missing");
        }
    }

    private static bool SourceMetadataChanged(
        DigestionLedgerSource source,
        RawChangeSet? changes) =>
        changes is null
        || changes.Paths.Any(path => path.Value ==
            $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml");

}
