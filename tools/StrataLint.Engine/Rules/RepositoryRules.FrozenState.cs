using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> FrozenStates(CurrentRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var affected = context.Current.Files.Values
            .Where(static file => FrozenStatePath.IsUnderRoot(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal).ToImmutableArray();
        if (affected.IsEmpty)
        {
            return findings.ToImmutable();
        }

        var states = LeanTruthStates.Resolve(context.Current, context.Lean);
        foreach (var file in affected)
        {
            var displayPath = "frozen state " + file.Path.Value;
            if (!FrozenStatePath.TryToModulePath(file.Path.Value, out var modulePath))
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    "path must encode exactly one canonical repository Lean module"));
                continue;
            }

            FrozenStateRecord record;
            try
            {
                record = FrozenStateRecordLoader.Load(file);
            }
            catch (FormatException exception)
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    exception.InnerException?.Message ?? exception.Message));
                continue;
            }

            if (!context.Current.Files.ContainsKey(modulePath))
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"module {modulePath.Value} does not exist"));
                continue;
            }

            if (!states.TryGetValue(modulePath, out var state) || state is not TruthState.Closed)
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"module {modulePath.Value} has TruthState={state}, expected Closed"));
                continue;
            }

            if (!context.Lean.Report.Files.TryGetValue(modulePath, out var report))
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"module {modulePath.Value} has no current Lean report"));
                continue;
            }

            if (!record.Declarations.SequenceEqual(FrozenStateRecord.Project(report)))
                findings.Add(new RuleFinding(displayPath, $"selector {modulePath.Value} declaration list mismatch with current report"));

            var actual = FrozenContentAddress.ComputeModuleStatementId(modulePath, report);
            if (record.StatementId != actual)
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"selector {modulePath.Value} pin mismatch: "
                    + $"stored={record.StatementId.Value} actual={actual.Value}"));
            }
        }

        return findings.ToImmutable();
    }

    private static void ObservePinChange(
        DeltaRuleContext context,
        RepositoryFile currentFile,
        RepoPath modulePath,
        FrozenStateRecord currentRecord,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!context.Baseline.Files.TryGetValue(currentFile.Path, out var baselineFile))
        {
            return;
        }

        try
        {
            var baselineRecord = FrozenStateRecordLoader.Load(baselineFile);
            if (baselineRecord.StatementId != currentRecord.StatementId)
            {
                findings.Add(new RuleFinding(
                    "frozen state " + currentFile.Path.Value,
                    $"FROZEN_PIN_CHANGE selector={modulePath.Value} "
                    + $"old={baselineRecord.StatementId.Value} new={currentRecord.StatementId.Value}",
                    AdmissionEffect.Observe));
            }
        }
        catch (FormatException)
        {
            // SL-008 judges only the candidate state; an unreadable old record cannot block it.
        }
    }
}
