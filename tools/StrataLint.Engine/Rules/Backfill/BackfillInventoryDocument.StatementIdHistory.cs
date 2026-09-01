using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed partial class BackfillInventoryDocument
{
    private static ImmutableArray<DigestionStatementIdHistoryEntry> ParseStatementIdHistory(
        string atomId,
        IReadOnlyDictionary<string, object?> receipt)
    {
        if (!receipt.ContainsKey("statement_id_history"))
        {
            return [];
        }

        var history = ImmutableArray.CreateBuilder<DigestionStatementIdHistoryEntry>();
        foreach (var rawHistory in List(
                     receipt,
                     "statement_id_history",
                     $"entry {atomId} statement_id_history must be a list"))
        {
            var item = Mapping(
                rawHistory,
                $"entry {atomId} statement_id_history item must be a mapping");
            ExactKeys(
                item,
                ["statement_id", "environment_pin", "superseded_by_pin"],
                $"entry {atomId} statement_id_history item");
            history.Add(new DigestionStatementIdHistoryEntry(
                Scalar(item, "statement_id", $"entry {atomId} historical statement_id"),
                ParseEffectiveLeanPins(atomId, item, "environment_pin"),
                ParseEffectiveLeanPins(atomId, item, "superseded_by_pin")));
        }

        if (history.Count == 0)
        {
            throw new FormatException(
                $"entry {atomId} statement_id_history must be omitted when empty");
        }

        return history.ToImmutable();
    }

    private static EffectiveLeanPins ParseEffectiveLeanPins(
        string atomId,
        IReadOnlyDictionary<string, object?> history,
        string key)
    {
        var pin = Mapping(
            history.GetValueOrDefault(key),
            $"entry {atomId} {key} must be a mapping");
        ExactKeys(pin, ["toolchain", "mathlib_revision"], $"entry {atomId} {key}");
        return new EffectiveLeanPins(
            Scalar(pin, "toolchain", $"entry {atomId} {key} toolchain"),
            Scalar(pin, "mathlib_revision", $"entry {atomId} {key} mathlib_revision"));
    }
}
