using System.Collections.Immutable;

namespace StrataLint.Scribe;

public enum LegacyAnchorDisposition
{
    Direct,
    Alias,
    RegisteredOpen,
    GrandfatheredUnresolved,
}

public abstract record LegacyAnchorEntry
{
    private protected LegacyAnchorEntry(
        string legacyValue,
        LegacyAnchorDisposition disposition,
        ImmutableArray<Anchor> canonicalTargets,
        string? caseId,
        string evidence)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(legacyValue);
        ArgumentException.ThrowIfNullOrWhiteSpace(evidence);
        LegacyValue = legacyValue;
        Disposition = disposition;
        CanonicalTargets = canonicalTargets;
        CaseId = caseId;
        Evidence = evidence;
    }

    public string LegacyValue { get; }

    public LegacyAnchorDisposition Disposition { get; }

    public ImmutableArray<Anchor> CanonicalTargets { get; }

    public string? CaseId { get; }

    public string Evidence { get; }

    public sealed record Alias : LegacyAnchorEntry
    {
        internal Alias(
            string legacyValue,
            LegacyAnchorDisposition disposition,
            ImmutableArray<Anchor> canonicalTargets,
            string? caseId,
            string evidence)
            : base(legacyValue, disposition, canonicalTargets, caseId, evidence)
        {
            if (disposition is LegacyAnchorDisposition.GrandfatheredUnresolved
                || canonicalTargets.IsDefaultOrEmpty
                || disposition is LegacyAnchorDisposition.RegisteredOpen && caseId is null
                || disposition is not LegacyAnchorDisposition.RegisteredOpen && caseId is not null)
            {
                throw new ArgumentException("Legacy alias has an invalid disposition.");
            }
        }
    }

    public sealed record GrandfatheredUnresolved : LegacyAnchorEntry
    {
        internal GrandfatheredUnresolved(
            string legacyValue,
            string caseId,
            string evidence)
            : base(
                legacyValue,
                LegacyAnchorDisposition.GrandfatheredUnresolved,
                ImmutableArray<Anchor>.Empty,
                caseId,
                evidence)
        {
            ArgumentException.ThrowIfNullOrWhiteSpace(caseId);
        }
    }
}

public static class LegacyAnchorEntries
{
    public static ImmutableArray<LegacyAnchorEntry> All { get; } =
        ImmutableArray.Create<LegacyAnchorEntry>(
        Direct("GICT-v3.6-I.1-definition-1.2", AnchorCatalogDefinitions.GictI1Definition1_2),
        Alias("GICT-v3.6-I.1-definition-1.4", [AnchorCatalogDefinitions.GictI2Definition1_4], "source-node-is-I.2-not-I.1"),
        Alias("GICT-v3.6-I.1-definitions-1.1-1.2", [AnchorCatalogDefinitions.GictI1Definition1_1, AnchorCatalogDefinitions.GictI1Definition1_2], "range-expanded-to-atomic-targets"),
        Direct("GICT-v3.6-I.1-theorem-1.3-i", AnchorCatalogDefinitions.GictI1Theorem1_3I),
        Direct("GICT-v3.6-I.1-theorem-1.3-ii", AnchorCatalogDefinitions.GictI1Theorem1_3II),
        Direct("GICT-v3.6-I.1-theorem-1.3-iii", AnchorCatalogDefinitions.GictI1Theorem1_3III),
        Alias("GICT-v3.6-I.1-theorem-1.3-iii-iv", [AnchorCatalogDefinitions.GictI1Theorem1_3III, AnchorCatalogDefinitions.GictI1Theorem1_3IV], "range-expanded-to-atomic-targets"),
        Direct("GICT-v3.6-I.2-definition-1.4", AnchorCatalogDefinitions.GictI2Definition1_4),
        Grandfather("GICT-v3.6-I.2-theorem-2.9", "D5-T0011", "literal-node-absent-from-frozen-gict"),
        Direct("GICT-v3.6-VIII-hearts", AnchorCatalogDefinitions.GictVIIIHearts),
        Direct("GICT-v3.6-appendix-A", AnchorCatalogDefinitions.GictAppendixA),
        Direct("PZG-v170-26.3", AnchorCatalogDefinitions.Pzg26_3),
        Direct("PZG-v170-26.4", AnchorCatalogDefinitions.Pzg26_4),
        Direct("PZG-v170-6.18", AnchorCatalogDefinitions.Pzg6_18),
        Direct("PZG-v170-6.19", AnchorCatalogDefinitions.Pzg6_19),
        Direct("golden-ledger-spec-v7.11-A1", AnchorCatalogDefinitions.SpecA1),
        Direct("golden-ledger-spec-v7.11-A11", AnchorCatalogDefinitions.SpecA11),
        Direct("golden-ledger-spec-v7.11-SL-002", AnchorCatalogDefinitions.SpecSl002),
        Direct("golden-ledger-spec-v7.11-SL-003", AnchorCatalogDefinitions.SpecSl003),
        Direct("golden-ledger-spec-v7.11-SL-014", AnchorCatalogDefinitions.SpecSl014),
        Direct("golden-ledger-spec-v7.11-SL-016", AnchorCatalogDefinitions.SpecSl016),
        Direct("golden-ledger-spec-v7.11-SL-017", AnchorCatalogDefinitions.SpecSl017),
        Direct("golden-ledger-spec-v7.11-SL-018", AnchorCatalogDefinitions.SpecSl018),
        Direct("golden-ledger-spec-v7.11-SL-019", AnchorCatalogDefinitions.SpecSl019),
        Direct("golden-ledger-spec-v7.11-byte-canonicalization", AnchorCatalogDefinitions.SpecByteCanonicalization),
        Direct("golden-ledger-spec-v7.11-human-gates", AnchorCatalogDefinitions.SpecHumanGates),
        Direct("golden-ledger-spec-v7.11-sample-11", AnchorCatalogDefinitions.SpecSample11),
        Open("mathlib-data-nat-fib-zeckendorf", AnchorCatalogDefinitions.MathlibZeckendorfModule, "D5-T0016"),
        Grandfather("paleywiener1934fourier", "D5-T0012", "local-library-target-missing"),
        Grandfather("sos1957threegap", "D5-T0012", "local-library-target-missing"))
        .OrderBy(static item => item.LegacyValue, StringComparer.Ordinal)
        .ToImmutableArray();

    private static LegacyAnchorEntry Direct(string legacy, Anchor target) =>
        new LegacyAnchorEntry.Alias(
            legacy,
            LegacyAnchorDisposition.Direct,
            [target],
            caseId: null,
            "mechanical-canonicalization");

    private static LegacyAnchorEntry Alias(
        string legacy,
        ImmutableArray<Anchor> targets,
        string evidence) =>
        new LegacyAnchorEntry.Alias(
            legacy,
            LegacyAnchorDisposition.Alias,
            targets,
            caseId: null,
            evidence);

    private static LegacyAnchorEntry Open(string legacy, Anchor target, string caseId) =>
        new LegacyAnchorEntry.Alias(
            legacy,
            LegacyAnchorDisposition.RegisteredOpen,
            [target],
            caseId,
            "external-receipt-open");

    private static LegacyAnchorEntry Grandfather(string legacy, string caseId, string evidence) =>
        new LegacyAnchorEntry.GrandfatheredUnresolved(legacy, caseId, evidence);
}
