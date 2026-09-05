using System.Collections.Immutable;

namespace StrataLint.Engine;

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
        DigestionLedgerEntry? atomTarget = null;
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

            if (softTarget.Kind is UtilityTargetKind.Atom)
            {
                var matches = backfill.RequireDigestionEntries()
                    .Where(entry => string.Equals(
                        entry.AtomId,
                        softTarget.Value,
                        StringComparison.Ordinal))
                    .ToArray();
                switch (matches)
                {
                    case []:
                        return Failure(
                            declaration,
                            UtilityValidationFailure.TargetDangling,
                            $"target={TargetDisplay(softTarget)}");
                    case [var only]:
                        atomTarget = only;
                        break;
                    default:
                        return Failure(
                            declaration,
                            UtilityValidationFailure.InputUnknown,
                            $"reason=ambiguous-atom-target:{softTarget.Value}");
                }
            }
            else if (!backfill.RequireTickets().Any(ticket => string.Equals(
                         ticket.CaseId,
                         softTarget.Value,
                         StringComparison.Ordinal)))
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
                atomTarget!,
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
