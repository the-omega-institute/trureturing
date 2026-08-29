namespace StrataLint.Engine;

internal static class LegacyFrozenLedgerEventSemantics
{
    internal static bool IsLegacySchemaVersion(int schemaVersion) =>
        schemaVersion is >= 2 and < FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion;

    internal static bool IsIdentityNeutral(string eventType) =>
        eventType is "Genesis" or "Reattest";
}
