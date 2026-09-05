using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum UtilityKind
{
    None,
    BoundedEnumeration,
    Checker,
    NumericReduction,
    CertifiedInstance,
}

internal enum UtilityBasisKind
{
    None,
    Consumer,
    Refutes,
    Terminal,
}

internal enum UtilityTargetKind
{
    Gid,
    Atom,
    Task,
}

internal enum UtilityParseFailure
{
    None,
    Missing,
    Syntax,
    InstanceMissing,
    PremisesMissing,
}

internal sealed record UtilityTarget(UtilityTargetKind Kind, string Value, Gid? Gid);

internal sealed record UtilityDeclaration(
    UtilityKind Kind,
    UtilityBasisKind BasisKind,
    UtilityTarget? BasisTarget,
    Gid? Instance,
    ImmutableArray<Gid> Premises,
    Gid? Result);

internal static class UtilitySyntax
{
    internal static bool TryParse(
        string? text,
        out UtilityDeclaration? utility,
        out UtilityParseFailure failure)
    {
        utility = null;
        failure = UtilityParseFailure.Syntax;
        if (text is null || string.Equals(text, "EDIT-ME", StringComparison.Ordinal))
        {
            failure = UtilityParseFailure.Missing;
            return false;
        }

        if (string.Equals(text, "none", StringComparison.Ordinal))
        {
            utility = new UtilityDeclaration(
                UtilityKind.None,
                UtilityBasisKind.None,
                null,
                null,
                [],
                null);
            failure = UtilityParseFailure.None;
            return true;
        }

        var encodedFields = text.Split("; ", StringSplitOptions.None);
        var fields = new List<(string Key, string Value)>();
        var keys = new HashSet<string>(StringComparer.Ordinal);
        foreach (var encodedField in encodedFields)
        {
            var separator = encodedField.IndexOf('=');
            if (separator <= 0
                || separator == encodedField.Length - 1
                || !keys.Add(encodedField[..separator]))
            {
                return false;
            }

            fields.Add((encodedField[..separator], encodedField[(separator + 1)..]));
        }

        if (fields.Count is < 2 or > 5
            || fields[0].Key != "kind"
            || fields[1].Key != "basis")
        {
            return false;
        }

        var optionalKeys = fields.Skip(2).Select(static field => field.Key).ToArray();
        var canonicalOptionalKeys = new[] { "instance", "premises", "result" }
            .Where(optionalKeys.Contains)
            .ToArray();
        if (!optionalKeys.SequenceEqual(canonicalOptionalKeys, StringComparer.Ordinal))
        {
            return false;
        }

        var kind = fields[0].Value switch
        {
            "bounded-enumeration" => UtilityKind.BoundedEnumeration,
            "checker" => UtilityKind.Checker,
            "numeric-reduction" => UtilityKind.NumericReduction,
            "certified-instance" => UtilityKind.CertifiedInstance,
            _ => (UtilityKind?)null,
        };
        if (kind is null || !TryParseBasis(fields[1].Value, out var basisKind, out var basisTarget))
        {
            return false;
        }

        Gid? instance = null;
        var premises = ImmutableArray<Gid>.Empty;
        Gid? result = null;
        foreach (var field in fields.Skip(2))
        {
            if (field.Key == "instance")
            {
                if (!TryParseDeclarationGid(field.Value, out instance)) return false;
            }
            else if (field.Key == "premises")
            {
                var parsed = ImmutableArray.CreateBuilder<Gid>();
                foreach (var item in field.Value.Split(',', StringSplitOptions.None))
                {
                    if (!TryParseDeclarationGid(item, out var premise)) return false;
                    parsed.Add(premise);
                }

                premises = parsed.ToImmutable();
            }
            else if (field.Key == "result")
            {
                if (!TryParseDeclarationGid(field.Value, out result)) return false;
            }
        }

        if (kind is UtilityKind.Checker && instance is null)
        {
            failure = UtilityParseFailure.InstanceMissing;
            return false;
        }

        if (kind is UtilityKind.NumericReduction && premises.IsEmpty)
        {
            failure = UtilityParseFailure.PremisesMissing;
            return false;
        }

        if (kind is UtilityKind.NumericReduction
            && basisKind is not (UtilityBasisKind.Consumer or UtilityBasisKind.Refutes))
        {
            return false;
        }

        utility = new UtilityDeclaration(
            kind.Value,
            basisKind,
            basisTarget,
            instance,
            premises,
            result);
        failure = UtilityParseFailure.None;
        return true;
    }

    private static bool TryParseBasis(
        string text,
        out UtilityBasisKind kind,
        out UtilityTarget? target)
    {
        kind = UtilityBasisKind.None;
        target = null;
        if (text.StartsWith("consumer=", StringComparison.Ordinal)
            && TryParseDeclarationGid(text["consumer=".Length..], out var consumer))
        {
            kind = UtilityBasisKind.Consumer;
            target = new UtilityTarget(UtilityTargetKind.Gid, consumer.Value, consumer);
            return true;
        }

        if (text.StartsWith("refutes=", StringComparison.Ordinal)
            && TryParseTarget(text["refutes=".Length..], out target))
        {
            kind = UtilityBasisKind.Refutes;
            return true;
        }

        if (text.StartsWith("terminal=", StringComparison.Ordinal)
            && TryParseTarget(text["terminal=".Length..], out target))
        {
            kind = UtilityBasisKind.Terminal;
            return true;
        }

        return false;
    }

    private static bool TryParseTarget(string text, out UtilityTarget? target)
    {
        target = null;
        if (text.StartsWith("atom:", StringComparison.Ordinal)
            && IsAtomId(text["atom:".Length..]))
        {
            target = new UtilityTarget(UtilityTargetKind.Atom, text["atom:".Length..], null);
            return true;
        }

        if (text.StartsWith("task:", StringComparison.Ordinal)
            && IsTaskCode(text["task:".Length..]))
        {
            target = new UtilityTarget(UtilityTargetKind.Task, text["task:".Length..], null);
            return true;
        }

        if (text.StartsWith("gid:", StringComparison.Ordinal)
            && TryParseDeclarationGid(text["gid:".Length..], out var gid))
        {
            target = new UtilityTarget(UtilityTargetKind.Gid, gid.Value, gid);
            return true;
        }

        return false;
    }

    private static bool IsAtomId(string value) =>
        value.Length == 64
        && value.All(static character =>
            character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static bool IsTaskCode(string value) =>
        value.Length == 8
        && value.StartsWith("D5-T", StringComparison.Ordinal)
        && value[4..].All(char.IsAsciiDigit);

    private static bool TryParseDeclarationGid(string text, out Gid gid)
    {
        if (Gid.TryParse(text, out var parsed)
            && parsed.ToTarget() is Target.Formal { Declaration: not null })
        {
            gid = parsed;
            return true;
        }

        gid = null!;
        return false;
    }
}

internal enum UtilityValidationPhase
{
    PreDeposit,
    FirstFreeze,
}

internal enum UtilityValidationFailure
{
    None,
    Missing,
    Syntax,
    InstanceMissing,
    PremisesMissing,
    InputUnknown,
    TargetDangling,
    RefutesAtomNoCoverage,
    ConsumerUnreachable,
}

internal sealed record UtilityValidationResult(
    UtilityDeclaration? Declaration,
    UtilityValidationFailure Failure,
    string Detail)
{
    internal bool IsAccepted => Failure is UtilityValidationFailure.None;
}

internal static class UtilityDeclarationValidator
{
    internal static UtilityValidationResult Validate(
        UtilityValidationPhase phase,
        RepoPath modulePath,
        string? text,
        RepositorySnapshot snapshot,
        Func<LeanAxiomReport> loadLeanReport)
    {
        ArgumentNullException.ThrowIfNull(modulePath);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(loadLeanReport);

        if (!UtilitySyntax.TryParse(text, out var declaration, out var parseFailure))
        {
            return new UtilityValidationResult(
                null,
                parseFailure switch
                {
                    UtilityParseFailure.Missing => UtilityValidationFailure.Missing,
                    UtilityParseFailure.InstanceMissing => UtilityValidationFailure.InstanceMissing,
                    UtilityParseFailure.PremisesMissing => UtilityValidationFailure.PremisesMissing,
                    _ => UtilityValidationFailure.Syntax,
                },
                string.Empty);
        }

        LeanAxiomReport? report = null;
        if (phase is UtilityValidationPhase.FirstFreeze
            || declaration!.Kind is not UtilityKind.None)
        {
            try
            {
                report = loadLeanReport();
            }
            catch (Exception exception) when (
                exception is InvalidOperationException
                    or FormatException
                    or ArgumentException
                    or IOException)
            {
                return Failure(
                    declaration!,
                    UtilityValidationFailure.InputUnknown,
                    "reason=current-lean-report-load-failed");
            }
        }

        LeanFileReport? moduleReport = null;
        if (phase is UtilityValidationPhase.FirstFreeze
            && (!report!.Files.TryGetValue(modulePath, out moduleReport)
                || moduleReport.Error is not null))
        {
            return Failure(
                declaration!,
                UtilityValidationFailure.InputUnknown,
                "reason=current-lean-report-missing");
        }

        if (declaration!.Kind is UtilityKind.None)
        {
            return Accepted(declaration);
        }

        foreach (var gid in DeclarationReferences(declaration))
        {
            var targetPath = ((Target.Formal)gid.ToTarget()).Path;
            if (!report!.Files.TryGetValue(targetPath, out var targetReport)
                || targetReport.Error is not null)
            {
                return Failure(
                    declaration,
                    UtilityValidationFailure.InputUnknown,
                    $"target_module={targetPath.Value} reason=current-lean-report-missing");
            }

            if (!TryResolveDeclaration(gid, targetReport, out _))
            {
                return Failure(
                    declaration,
                    UtilityValidationFailure.TargetDangling,
                    $"target={gid.Value}");
            }
        }

        BackfillInventoryDocument? backfill = null;
        var softTarget = declaration.BasisTarget;
        if (softTarget is { Kind: UtilityTargetKind.Atom or UtilityTargetKind.Task })
        {
            try
            {
                backfill = BackfillInventoryLoader.Load(snapshot);
            }
            catch (FormatException)
            {
                return Failure(
                    declaration,
                    UtilityValidationFailure.InputUnknown,
                    "reason=backfill-load-failed");
            }

            var targetExists = softTarget.Kind switch
            {
                UtilityTargetKind.Atom => backfill.RequireDigestionEntries()
                    .Any(entry => string.Equals(entry.AtomId, softTarget.Value, StringComparison.Ordinal)),
                UtilityTargetKind.Task => backfill.RequireTickets()
                    .Any(ticket => string.Equals(ticket.CaseId, softTarget.Value, StringComparison.Ordinal)),
                _ => true,
            };
            if (!targetExists)
            {
                return Failure(
                    declaration,
                    UtilityValidationFailure.TargetDangling,
                    $"target={TargetDisplay(softTarget)}");
            }
        }

        if (phase is UtilityValidationPhase.PreDeposit)
        {
            return Accepted(declaration);
        }

        if (declaration.BasisKind is UtilityBasisKind.Refutes
            && softTarget is { Kind: UtilityTargetKind.Atom }
            && !HasExactCoverage(
                backfill!.RequireDigestionEntries().Single(entry =>
                    string.Equals(entry.AtomId, softTarget.Value, StringComparison.Ordinal)),
                modulePath,
                moduleReport!))
        {
            return Failure(
                declaration,
                UtilityValidationFailure.RefutesAtomNoCoverage,
                $"atom={softTarget.Value}");
        }

        if (declaration.BasisKind is UtilityBasisKind.Consumer)
        {
            var consumerPath = ((Target.Formal)declaration.BasisTarget!.Gid!.ToTarget()).Path;
            var reachability = FindConsumerReachability(
                consumerPath,
                modulePath,
                snapshot,
                report!,
                out var unknownPath);
            if (reachability is ConsumerReachability.Unknown)
            {
                return Failure(
                    declaration,
                    UtilityValidationFailure.InputUnknown,
                    $"reason=consumer-path-input-missing:{unknownPath!.Value}");
            }

            if (reachability is ConsumerReachability.Unreachable)
            {
                return Failure(
                    declaration,
                    UtilityValidationFailure.ConsumerUnreachable,
                    $"consumer_module={consumerPath.Value}");
            }
        }

        return Accepted(declaration);
    }

    private static UtilityValidationResult Accepted(UtilityDeclaration declaration) =>
        new(declaration, UtilityValidationFailure.None, string.Empty);

    private static UtilityValidationResult Failure(
        UtilityDeclaration declaration,
        UtilityValidationFailure failure,
        string detail) =>
        new(declaration, failure, detail);

    private static IEnumerable<Gid> DeclarationReferences(UtilityDeclaration declaration)
    {
        if (declaration.BasisTarget?.Gid is { } basis)
        {
            yield return basis;
        }

        if (declaration.Instance is { } instance)
        {
            yield return instance;
        }

        foreach (var premise in declaration.Premises)
        {
            yield return premise;
        }

        if (declaration.Result is { } result)
        {
            yield return result;
        }
    }

    private static bool TryResolveDeclaration(
        Gid gid,
        LeanFileReport report,
        out LeanDeclaration? declaration)
    {
        var selector = ((Target.Formal)gid.ToTarget()).Declaration!;
        var matches = report.Declarations
            .Where(static item => item.IncludeInStatement)
            .Where(item => string.Equals(
                item.Name[(item.Name.LastIndexOf('.') + 1)..],
                selector,
                StringComparison.Ordinal))
            .ToArray();
        declaration = matches.Length == 1 ? matches[0] : null;
        return declaration is not null;
    }

    private static bool HasExactCoverage(
        DigestionLedgerEntry atom,
        RepoPath modulePath,
        LeanFileReport moduleReport) =>
        atom.Coverage.Any(edge =>
        {
            if (edge.TargetStatementId is null
                || !Gid.TryParse(edge.Gid, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null } target
                || target.Path != modulePath
                || !TryResolveDeclaration(gid, moduleReport, out var declaration))
            {
                return false;
            }

            return string.Equals(
                edge.TargetStatementId,
                CanonicalStatementWriter.DeclarationStatementId(modulePath, declaration!),
                StringComparison.Ordinal);
        });

    private static string TargetDisplay(UtilityTarget target) =>
        target.Kind switch
        {
            UtilityTargetKind.Gid => $"gid:{target.Value}",
            UtilityTargetKind.Atom => $"atom:{target.Value}",
            UtilityTargetKind.Task => $"task:{target.Value}",
            _ => throw new ArgumentOutOfRangeException(nameof(target)),
        };

    private enum ConsumerReachability
    {
        Reachable,
        Unreachable,
        Unknown,
    }

    private static ConsumerReachability FindConsumerReachability(
        RepoPath source,
        RepoPath target,
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        out RepoPath? unknownPath)
    {
        var managedPaths = snapshot.Files.Keys
            .Where(static path => LeanClosureValidator.IsManagedLean(path.Value))
            .ToImmutableHashSet();
        var pathsByModule = managedPaths
            .ToImmutableDictionary(LeanImportClosure.ModuleName, StringComparer.Ordinal);
        var pending = new Stack<RepoPath>();
        var visited = new HashSet<RepoPath>();
        var unknownPaths = new SortedSet<RepoPath>(
            Comparer<RepoPath>.Create(static (left, right) =>
                StringComparer.Ordinal.Compare(left.Value, right.Value)));
        pending.Push(source);
        while (pending.TryPop(out var current))
        {
            if (!visited.Add(current))
            {
                continue;
            }

            if (!report.Files.TryGetValue(current, out var currentReport)
                || currentReport.Error is not null)
            {
                unknownPaths.Add(current);
                continue;
            }

            if (current == target)
            {
                unknownPath = null;
                return ConsumerReachability.Reachable;
            }

            foreach (var import in currentReport.Imports
                         .Distinct(StringComparer.Ordinal)
                         .OrderByDescending(static value => value, StringComparer.Ordinal))
            {
                if (pathsByModule.TryGetValue(import, out var dependency))
                {
                    pending.Push(dependency);
                }
            }
        }

        unknownPath = unknownPaths.FirstOrDefault();
        return unknownPath is null
            ? ConsumerReachability.Unreachable
            : ConsumerReachability.Unknown;
    }
}

// SL-030. First-freeze utility admission for computational content.
internal static class UtilityAdmissionRule
{
    internal static bool IsAffectedBy(RuleEvaluationContext context) =>
        context.RuleImplementationChanged
        || context.Changes.Paths.Any(path =>
            FrozenStatePath.IsUnderRoot(path.Value)
            || path.Value.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
            || string.Equals(path.Value, BackfillInventoryLoader.RelativePath, StringComparison.Ordinal)
            || IsChangedUtilityHeader(context, path));

    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        AddRatchetFindings(context, findings);
        foreach (var change in context.Changes.Entries
                     .Where(static change =>
                         change.Kind is RawChangeKind.Added
                         && FrozenStatePath.IsUnderRoot(change.Path.Value))
                     .Where(change => context.Current.Files.ContainsKey(change.Path)
                         && !context.Baseline.Files.ContainsKey(change.Path))
                     .OrderBy(static change => change.Path.Value, StringComparer.Ordinal))
        {
            if (!FrozenStatePath.TryToModulePath(change.Path.Value, out var modulePath))
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    $"UTILITY-INPUT-UNKNOWN module={change.Path.Value} reason=invalid-frozen-state-path"));
                continue;
            }

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
                UtilityValidationPhase.FirstFreeze,
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

    private static void AddObservation(
        ImmutableArray<RuleFinding>.Builder findings,
        RepoPath modulePath,
        UtilityDeclaration? declaration)
    {
        var declaredFields = declaration is null
            ? "kind=unparsed"
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
        _ => throw new ArgumentOutOfRangeException(nameof(failure)),
    };

    private static string DetailSuffix(string detail) =>
        detail.Length == 0 ? string.Empty : " " + detail;
}
