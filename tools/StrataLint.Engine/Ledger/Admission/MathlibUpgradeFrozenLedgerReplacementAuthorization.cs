using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed class MathlibUpgradeFrozenLedgerReplacementAuthorization(
    RepositorySnapshot protectedBase, RepositorySnapshot candidate, FrozenStatementWitness? oldWitness = null)
{
    internal bool IsAuthorized(ImmutableHashSet<RepoPath> changedPaths, FrozenStateCatalog baseState,
        LeanAxiomReport candidateReport)
    {
        var currentState = FrozenStateCatalog.Load(candidate);
        var retained = baseState.Records.Keys.Where(currentState.Records.ContainsKey).ToImmutableHashSet();
        return changedPaths.IsSubsetOf(retained)
        && EffectiveLeanPins.TryRead(protectedBase, out var basePins)
        && EffectiveLeanPins.TryRead(candidate, out var candidatePins) && basePins != candidatePins
        && LeanPropositionSourceComparer.AreEquivalent(protectedBase, candidate, changedPaths, baseState, candidateReport, oldWitness)
        && retained.All(path => candidateReport.Files.TryGetValue(path, out var module)
            && module.Declarations.All(static declaration => declaration.Axioms.All(LeanAxiomFacts.IsStandard)));
    }
}

internal sealed record EffectiveLeanPins(string Toolchain, string MathlibRevision)
{
    internal static bool TryRead(
        RepositorySnapshot snapshot,
        out EffectiveLeanPins? pins)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        pins = null;
        if (!snapshot.TryGetFile("lean-toolchain", out var toolchainFile)
            || !snapshot.TryGetFile("lake-manifest.json", out var manifestFile)
            || !TryReadToolchain(toolchainFile.Text, out var toolchain)
            || !TryReadMathlibRevision(manifestFile.RawBytes, out var revision))
        {
            return false;
        }

        pins = new EffectiveLeanPins(toolchain, revision);
        return true;
    }

    private static bool TryReadToolchain(string text, out string toolchain)
    {
        var values = text.Split('\n')
            .Select(static line => line.Trim())
            .Where(static line => line.Length > 0 && !line.StartsWith('#'))
            .ToImmutableArray();
        if (values.Length != 1
            || values[0].Any(char.IsWhiteSpace)
            || values[0].Contains('#', StringComparison.Ordinal))
        {
            toolchain = string.Empty;
            return false;
        }

        toolchain = values[0];
        return true;
    }

    private static bool TryReadMathlibRevision(
        ImmutableArray<byte> bytes,
        out string revision)
    {
        revision = string.Empty;
        try
        {
            using var document = JsonDocument.Parse(bytes.ToArray());
            var root = document.RootElement;
            if (root.ValueKind is not JsonValueKind.Object
                || !root.TryGetProperty("packages", out var packages)
                || packages.ValueKind is not JsonValueKind.Array)
            {
                return false;
            }

            var mathlib = packages.EnumerateArray()
                .Where(static package => package.ValueKind is JsonValueKind.Object
                    && package.TryGetProperty("name", out var name)
                    && name.ValueKind is JsonValueKind.String
                    && name.GetString() == "mathlib")
                .ToImmutableArray();
            if (mathlib.Length != 1
                || !mathlib[0].TryGetProperty("type", out var type)
                || type.ValueKind is not JsonValueKind.String
                || type.GetString() != "git"
                || !mathlib[0].TryGetProperty("rev", out var rev)
                || rev.ValueKind is not JsonValueKind.String)
            {
                return false;
            }

            var raw = rev.GetString()!;
            if (raw.Length is not (40 or 64) || raw.Any(static value =>
                !char.IsAsciiHexDigit(value)))
            {
                return false;
            }

            revision = raw.ToLowerInvariant();
            return true;
        }
        catch (JsonException)
        {
            return false;
        }
    }
}
