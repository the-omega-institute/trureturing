using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

internal enum C0AnchorKind
{
    Controller,
    Corpus,
    GateWiring,
}

internal sealed record C0Anchor(C0AnchorKind Kind, string Path);

internal static class C0CeremonyProjection
{
    internal const string ComponentId = "conservative-extension-gate-c";
    internal const string CertificatePath =
        "Meta/StrataLint/Golden/c0-inaugural-conservative-certificate.json";
    internal const string CliApplicationPath =
        "Meta/StrataLint/StrataLint.Cli/Commands/CliApplication.cs";
    internal const string ProductionEnvironmentPath =
        "Meta/StrataLint/StrataLint.Cli/Admission/ProductionCliEnvironment.cs";
    internal const string GitRepositoryGatewaySourcePath =
        "Meta/StrataLint/StrataLint.Cli/Admission/GitRepositoryGateway.cs";
    internal const string GitRepositoryGatewayFrozenLedgerSourcePath =
        "Meta/StrataLint/StrataLint.Cli/Admission/GitRepositoryGateway.FrozenLedger.cs";
    internal const string FrozenEvidenceResolverSourcePath =
        "Meta/StrataLint/StrataLint.Cli/Admission/FrozenEvidenceResolver.cs";
    internal const string ProgramPath = "Meta/StrataLint/StrataLint.Cli/Program.cs";
    internal const string ProjectionSourcePath =
        "Meta/StrataLint/StrataLint.Engine/Coverage/C0CeremonyProjection.cs";
    internal const string ActualValidatorPath =
        "Meta/StrataLint/StrataLint.Engine/Coverage/TowerActualValidator.cs";
    internal const string TowerManifestSourcePath =
        "Meta/StrataLint/StrataLint.Engine/Coverage/TowerManifest.cs";
    internal const string TowerParserSourcePath =
        "Meta/StrataLint/StrataLint.Engine/Coverage/TowerManifestParser.cs";
    internal const string FixtureRegistryPath = "Golden/fixture-registry.yaml";
    internal const string ValuesKernelDataPath = "Golden/values-kernels.toml";
    internal const string GateWiringPath = ".github/scripts/harness-gate.sh";
    internal const string LocalGateWiringPath =
        "Meta/StrataLint/scripts/local-harness-gate.sh";
    internal const string LeanReportPairPath =
        "Meta/StrataLint/scripts/lean-report-pair.sh";
    internal const string LeanInspectorScriptPath =
        "Meta/StrataLint/lean-inspector/inspect.sh";
    internal const string LeanInspectorSourcePath =
        "Meta/StrataLint/lean-inspector/Inspector.lean";

    private const string ControllerDirectory =
        "Meta/StrataLint/StrataLint.Cli/Conservative/";
    private const string CorpusSourceDirectory =
        "Meta/StrataLint/StrataLint.Cli/Golden/";
    private const string CorpusDataDirectory = "Golden/cases/";

    private static readonly ImmutableArray<string> Phases =
    [
        "phase1-protected-content-admission",
        "phase2-dual-harness-conservative-extension",
    ];

    private static readonly ImmutableArray<C0Anchor> FixedAnchors =
    [
        new(C0AnchorKind.Controller, CliApplicationPath),
        new(C0AnchorKind.Controller, ProductionEnvironmentPath),
        new(C0AnchorKind.Controller, GitRepositoryGatewaySourcePath),
        new(C0AnchorKind.Controller, GitRepositoryGatewayFrozenLedgerSourcePath),
        new(C0AnchorKind.Controller, FrozenEvidenceResolverSourcePath),
        new(C0AnchorKind.Controller, ProgramPath),
        new(C0AnchorKind.Controller, ProjectionSourcePath),
        new(C0AnchorKind.Controller, ActualValidatorPath),
        new(C0AnchorKind.Controller, TowerManifestSourcePath),
        new(C0AnchorKind.Controller, TowerParserSourcePath),
        new(C0AnchorKind.Corpus, FixtureRegistryPath),
        new(C0AnchorKind.Corpus, ValuesKernelDataPath),
        new(C0AnchorKind.GateWiring, GateWiringPath),
        // The base-owned conservative grammar permits exactly one gate-wiring record.
        new(C0AnchorKind.Controller, LocalGateWiringPath),
        new(C0AnchorKind.Controller, LeanReportPairPath),
        new(C0AnchorKind.Controller, LeanInspectorScriptPath),
        new(C0AnchorKind.Controller, LeanInspectorSourcePath),
    ];

    internal static ImmutableArray<C0Anchor> DiscoverAnchors(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var anchors = FixedAnchors
            .Concat(Discover(snapshot, ControllerDirectory, ".cs", C0AnchorKind.Controller))
            .Concat(Discover(snapshot, CorpusSourceDirectory, ".cs", C0AnchorKind.Corpus))
            .Concat(Discover(snapshot, CorpusDataDirectory, ".toml", C0AnchorKind.Corpus))
            .Distinct()
            .OrderBy(static item => item.Kind)
            .ThenBy(static item => item.Path, StringComparer.Ordinal)
            .ToImmutableArray();
        var collision = anchors
            .GroupBy(static item => item.Path, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Select(static item => item.Kind).Distinct().Count() > 1);
        if (collision is not null)
        {
            throw new InvalidOperationException(
                $"C0 anchor is assigned to multiple kinds: {collision.Key}");
        }

        return anchors;
    }

    internal static bool HasCanonicalShape(IReadOnlyList<string> members)
    {
        if (!HasCanonicalPhases(members))
        {
            return false;
        }

        var records = members.Skip(Phases.Length).ToArray();
        if (!records.SequenceEqual(records.Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            return false;
        }

        var counts = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var record in records)
        {
            var fields = record.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            var kind = fields[0];
            var valid = fields switch
            {
                ["c0/ceremony-commit", "convention/this-pr-merge-commit"] => true,
                ["c0/inaugural-certificate", var digest, var path] =>
                    IsTaggedLowerHex(digest, "sha256/", 64)
                    && path == CertificatePath,
                ["c0/preimage-tree", var oid] => IsTaggedLowerHex(oid, "git-tree/", 40),
                _ => false,
            };
            if (!valid) return false;
            counts[kind] = counts.GetValueOrDefault(kind) + 1;
        }

        return records.Length == 3
            && Count(counts, "c0/ceremony-commit") == 1
            && Count(counts, "c0/inaugural-certificate") == 1
            && Count(counts, "c0/preimage-tree") == 1;
    }

    internal static bool HasCanonicalPhases(IReadOnlyList<string> members) =>
        members.Count >= Phases.Length
        && members.Take(Phases.Length).SequenceEqual(Phases, StringComparer.Ordinal);

    internal static bool TrustRootMatchesSnapshot(
        IReadOnlyList<string> members,
        RepositorySnapshot snapshot,
        out string reason)
    {
        try
        {
            if (!snapshot.TryGetFile(CertificatePath, out var certificate))
            {
                reason = $"certificate is missing: {CertificatePath}";
                return false;
            }

            var records = members.Skip(Phases.Length).ToArray();
            var certificateRecord = records.Single(static member =>
                member.StartsWith("c0/inaugural-certificate ", StringComparison.Ordinal));
            var expectedCertificate = "c0/inaugural-certificate sha256/"
                + Convert.ToHexStringLower(SHA256.HashData(certificate.RawBytes.AsSpan()))
                + " " + CertificatePath;
            if (certificateRecord != expectedCertificate)
            {
                reason = "inaugural certificate address does not match its frozen bytes";
                return false;
            }

            using var document = JsonDocument.Parse(certificate.RawBytes.ToArray());
            var treeOid = document.RootElement.GetProperty("candidate").GetProperty("tree_oid").GetString();
            var expectedTree = "c0/preimage-tree git-tree/"
                + Untag(treeOid, "git-sha1:");
            if (!records.Contains(expectedTree, StringComparer.Ordinal))
            {
                reason = "preimage tree does not match the inaugural certificate";
                return false;
            }

            reason = string.Empty;
            return true;
        }
        catch (Exception exception) when (exception is InvalidOperationException
            or FormatException
            or JsonException
            or KeyNotFoundException)
        {
            reason = exception.Message;
            return false;
        }
    }

    internal static bool TryCreateAnchorCustodianReferences(
        RepositorySnapshot snapshot,
        out ImmutableArray<string> records)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var builder = ImmutableArray.CreateBuilder<string>();
        foreach (var anchor in DiscoverAnchors(snapshot))
        {
            if (!snapshot.TryGetFile(anchor.Path, out var file))
            {
                records = ImmutableArray<string>.Empty;
                return false;
            }

            var kind = anchor.Kind switch
            {
                C0AnchorKind.Controller => "c0/controller",
                C0AnchorKind.Corpus => "c0/corpus",
                C0AnchorKind.GateWiring => "c0/gate-wiring",
                _ => throw new InvalidOperationException("unknown C0 anchor kind"),
            };
            var address = FrozenContentAddress.ComputeGitBlobOid(
                file.RawBytes.AsSpan(),
                HashAlgorithmName.SHA1).Replace(':', '/');
            builder.Add($"{kind} {address} {anchor.Path}");
        }

        records = builder.Order(StringComparer.Ordinal).ToImmutableArray();
        return true;
    }

    private static IEnumerable<C0Anchor> Discover(
        RepositorySnapshot snapshot,
        string prefix,
        string extension,
        C0AnchorKind kind) => snapshot.Files.Keys
        .Select(static path => path.Value)
        .Where(path => path.StartsWith(prefix, StringComparison.Ordinal)
            && path.EndsWith(extension, StringComparison.Ordinal))
        .Select(path => new C0Anchor(kind, path));

    private static int Count(IReadOnlyDictionary<string, int> counts, string kind) =>
        counts.GetValueOrDefault(kind);

    private static string Untag(string? value, string prefix)
    {
        if (value is null || !value.StartsWith(prefix, StringComparison.Ordinal))
        {
            throw new FormatException($"C0 certificate tree must start with {prefix}");
        }

        var untagged = value[prefix.Length..];
        if (untagged.Length != 40 || untagged.Any(static character =>
                character is not (>= '0' and <= '9' or >= 'a' and <= 'f')))
        {
            throw new FormatException("C0 certificate tree must be 40 lowercase hexadecimal digits");
        }

        return untagged;
    }

    private static bool IsTaggedLowerHex(string value, string prefix, int digits) =>
        value.StartsWith(prefix, StringComparison.Ordinal)
        && value.Length == prefix.Length + digits
        && value[prefix.Length..].All(static character =>
            character is >= '0' and <= '9' or >= 'a' and <= 'f');

}

internal static class C0TowerProjection
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ImmutableArray<byte> Write(
        ReadOnlySpan<byte> towerBytes,
        ImmutableArray<string> members)
    {
        var parsed = TowerManifestParser.Parse(towerBytes) switch
        {
            TowerManifestParseOutcome.Loaded loaded => loaded.Syntax,
            TowerManifestParseOutcome.Invalid invalid =>
                throw new FormatException($"TOWER is invalid: {invalid.Message}"),
        };
        var component = parsed.Components.SingleOrDefault(static item =>
            item.Id == C0CeremonyProjection.ComponentId)
            ?? throw new FormatException("TOWER C0 component is missing or duplicated");
        if (component.Kind != "phased-gate")
        {
            throw new FormatException("TOWER C0 component is not a phased gate");
        }

        var text = StrictUtf8.GetString(towerBytes);
        if (text.Contains('\r') || !text.EndsWith('\n'))
        {
            throw new FormatException("TOWER must use canonical LF text with a final newline");
        }

        var componentMarker = "  - id: " + C0CeremonyProjection.ComponentId + "\n";
        var componentStart = UniqueIndexOf(text, componentMarker, "C0 component");
        var membersMarker = "    members:\n";
        var membersStart = text.IndexOf(
            membersMarker,
            componentStart + componentMarker.Length,
            StringComparison.Ordinal);
        var membersEnd = text.IndexOf(
            "    judged_by:\n",
            membersStart + membersMarker.Length,
            StringComparison.Ordinal);
        if (membersStart < 0 || membersEnd < 0)
        {
            throw new FormatException("TOWER C0 member block is not canonical");
        }

        var block = new StringBuilder(membersMarker);
        foreach (var member in members)
        {
            if (member.Contains('"') || member.Contains('\\') || member.Contains('\n'))
            {
                throw new FormatException("C0 member cannot be represented canonically in TOWER");
            }

            block.Append("      - ");
            if (member.StartsWith("c0/", StringComparison.Ordinal)) block.Append('"');
            block.Append(member);
            if (member.StartsWith("c0/", StringComparison.Ordinal)) block.Append('"');
            block.Append('\n');
        }

        var output = text[..membersStart] + block + text[membersEnd..];
        var bytes = ImmutableArray.CreateRange(StrictUtf8.GetBytes(output));
        var reparsed = TowerManifestParser.Parse(bytes.AsSpan()) switch
        {
            TowerManifestParseOutcome.Loaded loaded => loaded.Syntax,
            TowerManifestParseOutcome.Invalid invalid =>
                throw new FormatException($"generated TOWER is invalid: {invalid.Message}"),
        };
        var generated = reparsed.Components.Single(static item =>
            item.Id == C0CeremonyProjection.ComponentId);
        if (!generated.Members.SequenceEqual(members, StringComparer.Ordinal))
        {
            throw new InvalidOperationException("generated TOWER C0 members did not round-trip");
        }

        return bytes;
    }

    private static int UniqueIndexOf(string text, string value, string label)
    {
        var first = text.IndexOf(value, StringComparison.Ordinal);
        if (first < 0 || text.IndexOf(value, first + value.Length, StringComparison.Ordinal) >= 0)
        {
            throw new FormatException($"TOWER {label} is missing or duplicated");
        }

        return first;
    }
}
