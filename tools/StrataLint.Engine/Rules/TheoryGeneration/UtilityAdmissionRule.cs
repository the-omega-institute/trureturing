using System.Collections.Immutable;

namespace StrataLint.Engine;

// SL-031. Changed unfrozen content and first-freeze utility admission.
internal static class UtilityAdmissionRule
{
    internal static bool IsAffectedBy(RuleEvaluationContext context) =>
        context.RuleImplementationChanged
        || SelectedPaths(context).Any()
        || context.Changes.Paths.Any(path => IsBaselineFrozen(context, path)
            && IsChangedUtilityHeader(context, path));

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        AddRatchetFindings(context, findings);
        var modules = new Dictionary<RepoPath, UtilityValidationPhase>();
        foreach (var path in SelectedPaths(context))
        {
            if (!FrozenStatePath.IsUnderRoot(path.Value))
            {
                modules.TryAdd(path, UtilityValidationPhase.ChangedContent);
                continue;
            }

            if (!FrozenStatePath.TryToModulePath(path.Value, out var modulePath))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"UTILITY-INPUT-UNKNOWN module={path.Value} reason=invalid-frozen-state-path"));
                continue;
            }

            modules[modulePath] = UtilityValidationPhase.FirstFreeze;
        }

        foreach (var (modulePath, phase) in modules.OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
        {
            AddClassificationFindings(context, modulePath, findings);
            if (!context.Current.TryGetFile(modulePath.Value, out var module)
                || !RepositoryRules.TryHeader(module.Text, out var header))
            {
                AddObservation(findings, modulePath, declaration: null);
                findings.Add(new RuleFinding(
                    modulePath.Value,
                    $"UTILITY-MISSING module={modulePath.Value}"));
                continue;
            }

            var validation = UtilityDeclarationValidator.Validate(
                phase,
                modulePath,
                header.Utility,
                context.Current,
                () => context.Lean.Report);
            AddObservation(findings, modulePath, validation.Declaration);
            if (!validation.IsAccepted)
            {
                findings.Add(new RuleFinding(
                    modulePath.Value,
                    $"{RuleFailureCode(validation.Failure)} module={modulePath.Value}"
                    + DetailSuffix(validation.Detail)));
                continue;
            }
        }

        return findings.ToImmutable();
    }

    private static IEnumerable<RepoPath> SelectedPaths(RuleEvaluationContext context) =>
        context.Changes.Paths.Where(path =>
            context.Current.Files.TryGetValue(path, out var current)
            && (FrozenStatePath.IsUnderRoot(path.Value)
                ? !context.Baseline.Files.ContainsKey(path)
                : IsD5Lean(path.Value)
                    && !IsBaselineFrozen(context, path)
                    && (!context.Baseline.Files.TryGetValue(path, out var baseline)
                        || !current.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan()))));

    private static bool IsBaselineFrozen(RuleEvaluationContext context, RepoPath path) =>
        IsD5Lean(path.Value)
        && FrozenStatePath.TryFromModulePath(path, out var statePath)
        && context.Baseline.Files.ContainsKey(statePath);

    private static void AddClassificationFindings(
        RuleEvaluationContext context,
        RepoPath path,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!context.Baseline.Files.TryGetValue(path, out var baseline)
            || !context.Current.Files.TryGetValue(path, out var current))
        {
            return;
        }

        var before = ClassificationDisplay(baseline);
        var after = ClassificationDisplay(current);
        if (before == after) return;
        findings.Add(new RuleFinding(path.Value,
            $"UTILITY-CLASSIFICATION-CHANGED module={path.Value} "
            + $"before={before} after={after} semantics=unverified-by-machine",
            AdmissionEffect.Observe));
        if (UtilityDeclarationValidator.IsClassificationDowngrade(baseline, current))
        {
            findings.Add(new RuleFinding(path.Value,
                $"UTILITY-CLASSIFICATION-DOWNGRADE module={path.Value} reason=ordinary-body-unchanged"));
        }
    }

    private static string ClassificationDisplay(RepositoryFile file)
    {
        if (!RepositoryRules.TryHeader(file.Text, out var header) || header.Utility is null)
            return "missing";
        return UtilitySyntax.TryParse(header.Utility, out var declaration, out _)
            ? KindDisplay(declaration!.Kind)
            : "unparsed";
    }

    private static void AddObservation(
        ImmutableArray<RuleFinding>.Builder findings,
        RepoPath modulePath,
        UtilityDeclaration? declaration)
    {
        var declaredFields = declaration is null
            ? "kind=unparsed basis=n/a target=n/a"
            : $"kind={KindDisplay(declaration.Kind)} "
                + $"basis={BasisDisplay(declaration.BasisKind)} "
                + $"target={BasisTargetDisplay(declaration)}";
        findings.Add(new RuleFinding(
            modulePath.Value,
            $"UTILITY-OBSERVED module={modulePath.Value} {declaredFields} "
            + "semantics=unverified-by-machine",
            AdmissionEffect.Observe));
    }

    private static void AddRatchetFindings(
        RuleEvaluationContext context,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        foreach (var path in context.Changes.Paths
                     .Where(static path => IsD5Lean(path.Value))
                     .OrderBy(static path => path.Value, StringComparer.Ordinal))
        {
            if (!FrozenStatePath.TryFromModulePath(path, out var statePath)
                || !context.Baseline.Files.ContainsKey(statePath)
                || !IsChangedUtilityHeader(context, path))
            {
                continue;
            }

            findings.Add(new RuleFinding(
                path.Value,
                $"UTILITY-RATCHET module={path.Value}"));
        }
    }

    private static bool IsChangedUtilityHeader(RuleEvaluationContext context, RepoPath path)
    {
        if (!IsD5Lean(path.Value))
        {
            return false;
        }

        var baselineValid = TryGetUtility(context.Baseline, path, out var baselineUtility);
        var currentValid = TryGetUtility(context.Current, path, out var currentUtility);
        if (!baselineValid || !currentValid)
        {
            return baselineValid != currentValid;
        }

        return !string.Equals(
            baselineUtility,
            currentUtility,
            StringComparison.Ordinal);
    }

    private static bool TryGetUtility(
        RepositorySnapshot snapshot,
        RepoPath path,
        out string? utility)
    {
        utility = null;
        if (!snapshot.TryGetFile(path.Value, out var file)
            || !RepositoryRules.TryHeader(file.Text, out var header))
        {
            return false;
        }

        utility = header.Utility;
        return true;
    }

    private static bool IsD5Lean(string path) =>
        path.StartsWith("D5/", StringComparison.Ordinal)
        && path.EndsWith(".lean", StringComparison.Ordinal);

    private static string KindDisplay(UtilityKind kind) => kind switch
    {
        UtilityKind.None => "none",
        UtilityKind.BoundedEnumeration => "bounded-enumeration",
        UtilityKind.Checker => "checker",
        UtilityKind.NumericReduction => "numeric-reduction",
        UtilityKind.CertifiedInstance => "certified-instance",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };

    private static string BasisDisplay(UtilityBasisKind kind) => kind switch
    {
        UtilityBasisKind.None => "none",
        UtilityBasisKind.Consumer => "consumer",
        UtilityBasisKind.Refutes => "refutes",
        UtilityBasisKind.Terminal => "terminal",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };

    private static string BasisTargetDisplay(UtilityDeclaration utility) =>
        utility.BasisTarget is null
            ? "none"
            : utility.BasisKind is UtilityBasisKind.Consumer
                ? utility.BasisTarget.Value
                : TargetDisplay(utility.BasisTarget);

    private static string TargetDisplay(UtilityTarget target) =>
        target.Kind switch
        {
            UtilityTargetKind.Gid => $"gid:{target.Value}",
            UtilityTargetKind.Atom => $"atom:{target.Value}",
            UtilityTargetKind.Task => $"task:{target.Value}",
            _ => throw new ArgumentOutOfRangeException(nameof(target)),
        };

    private static string RuleFailureCode(UtilityValidationFailure failure) => failure switch
    {
        UtilityValidationFailure.Missing => "UTILITY-MISSING",
        UtilityValidationFailure.Syntax => "UTILITY-SYNTAX",
        UtilityValidationFailure.InstanceMissing => "UTILITY-INSTANCE-MISSING",
        UtilityValidationFailure.PremisesMissing => "UTILITY-PREMISES-MISSING",
        UtilityValidationFailure.InputUnknown => "UTILITY-INPUT-UNKNOWN",
        UtilityValidationFailure.TargetDangling => "UTILITY-TARGET-DANGLING",
        UtilityValidationFailure.RefutesAtomNoCoverage => "UTILITY-REFUTES-ATOM-NO-COVERAGE",
        UtilityValidationFailure.ConsumerUnreachable => "UTILITY-CONSUMER-UNREACHABLE",
        UtilityValidationFailure.OrdinaryInstanceForbidden => "UTILITY-ORDINARY-INSTANCE-BANNED",
        UtilityValidationFailure.ClassificationDowngrade => "UTILITY-CLASSIFICATION-DOWNGRADE",
        UtilityValidationFailure.RefutationInvalid => "UTILITY-REFUTATION-INVALID",
        UtilityValidationFailure.RefutationEvidenceMissing => "UTILITY-REFUTATION-EVIDENCE-MISSING",
        _ => throw new ArgumentOutOfRangeException(nameof(failure)),
    };

    private static string DetailSuffix(string detail) =>
        detail.Length == 0 ? string.Empty : " " + detail;
}
