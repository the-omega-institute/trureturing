namespace StrataLint.Engine;

internal static class LegacyFrozenLedgerEventSemantics
{
    internal static bool IsIdentityNeutral(string eventType) =>
        eventType is "Genesis" or "Reattest";
}
