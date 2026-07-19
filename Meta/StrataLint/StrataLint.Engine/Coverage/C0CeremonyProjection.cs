using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal enum C0AnchorKind
{
    Controller,
    Corpus,
    GateWiring,
}

internal sealed record C0Anchor(C0AnchorKind Kind, string Path);

internal sealed record C0CeremonyIdentity(
    string BaseCommitOid,
    string PreimageCommitOid,
    string PreimageTreeOid);

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

    internal static ImmutableArray<string> CreateMembers(
        RepositorySnapshot snapshot,
        ReadOnlySpan<byte> certificateBytes,
        C0CeremonyIdentity identity)
    {
        ArgumentNullException.ThrowIfNull(identity);
        RequireLowerHex(identity.BaseCommitOid, 40, "base commit");
        RequireLowerHex(identity.PreimageCommitOid, 40, "preimage commit");
        RequireLowerHex(identity.PreimageTreeOid, 40, "preimage tree");
        var records = CreateAddressRecords(snapshot, certificateBytes)
            .Add("c0/base-commit git-commit/" + identity.BaseCommitOid)
            .Add("c0/ceremony-commit convention/this-pr-merge-commit")
            .Add("c0/preimage-commit git-commit/" + identity.PreimageCommitOid)
            .Add("c0/preimage-tree git-tree/" + identity.PreimageTreeOid)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        return Phases.AddRange(records);
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
        var addressedPaths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var record in records)
        {
            var fields = record.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            var kind = fields[0];
            var valid = fields switch
            {
                ["c0/base-commit", var oid] => IsTaggedLowerHex(oid, "git-commit/", 40),
                ["c0/ceremony-commit", "convention/this-pr-merge-commit"] => true,
                ["c0/controller" or "c0/corpus" or "c0/gate-wiring", var oid, var path] =>
                    IsTaggedLowerHex(oid, "git-sha1/", 40)
                    && IsRepositoryPath(path)
                    && addressedPaths.Add(kind + " " + path),
                ["c0/inaugural-certificate", var digest, var path] =>
                    IsTaggedLowerHex(digest, "sha256/", 64)
                    && IsRepositoryPath(path)
                    && addressedPaths.Add(kind + " " + path),
                ["c0/preimage-commit", var oid] => IsTaggedLowerHex(oid, "git-commit/", 40),
                ["c0/preimage-tree", var oid] => IsTaggedLowerHex(oid, "git-tree/", 40),
                _ => false,
            };
            if (!valid) return false;
            counts[kind] = counts.GetValueOrDefault(kind) + 1;
        }

        return Count(counts, "c0/base-commit") == 1
            && Count(counts, "c0/ceremony-commit") == 1
            && Count(counts, "c0/controller") > 0
            && Count(counts, "c0/corpus") > 0
            && Count(counts, "c0/gate-wiring") == 1
            && Count(counts, "c0/inaugural-certificate") == 1
            && Count(counts, "c0/preimage-commit") == 1
            && Count(counts, "c0/preimage-tree") == 1;
    }

    internal static bool HasCanonicalPhases(IReadOnlyList<string> members) =>
        members.Count >= Phases.Length
        && members.Take(Phases.Length).SequenceEqual(Phases, StringComparer.Ordinal);

    internal static bool AddressesMatchSnapshot(
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

            var expected = CreateAddressRecords(snapshot, certificate.RawBytes.AsSpan());
            var actual = members
                .Skip(Phases.Length)
                .Where(static member => member.StartsWith("c0/controller ", StringComparison.Ordinal)
                    || member.StartsWith("c0/corpus ", StringComparison.Ordinal)
                    || member.StartsWith("c0/gate-wiring ", StringComparison.Ordinal)
                    || member.StartsWith("c0/inaugural-certificate ", StringComparison.Ordinal))
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            if (!actual.SequenceEqual(expected, StringComparer.Ordinal))
            {
                reason = $"declared {actual.Length} addressed records but canonical policy produced {expected.Length}";
                return false;
            }

            reason = string.Empty;
            return true;
        }
        catch (Exception exception) when (exception is InvalidOperationException or FormatException)
        {
            reason = exception.Message;
            return false;
        }
    }

    private static ImmutableArray<string> CreateAddressRecords(
        RepositorySnapshot snapshot,
        ReadOnlySpan<byte> certificateBytes)
    {
        if (!TryCreateAnchorAddressRecords(snapshot, out var anchorRecords))
        {
            var missing = DiscoverAnchors(snapshot).First(anchor =>
                !snapshot.TryGetFile(anchor.Path, out _));
            throw new InvalidOperationException($"C0 anchor is missing: {missing.Path}");
        }

        var records = anchorRecords.ToBuilder();
        var certificateAddress = "sha256/"
            + Convert.ToHexStringLower(SHA256.HashData(certificateBytes));
        records.Add($"c0/inaugural-certificate {certificateAddress} {CertificatePath}");
        return records.Order(StringComparer.Ordinal).ToImmutableArray();
    }

    internal static bool TryCreateAnchorAddressRecords(
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

    private static void RequireLowerHex(string value, int digits, string label)
    {
        if (value.Length != digits || value.Any(static character =>
                character is not (>= '0' and <= '9' or >= 'a' and <= 'f')))
        {
            throw new FormatException($"C0 {label} must be {digits} lowercase hexadecimal digits");
        }
    }

    private static bool IsTaggedLowerHex(string value, string prefix, int digits) =>
        value.StartsWith(prefix, StringComparison.Ordinal)
        && value.Length == prefix.Length + digits
        && value[prefix.Length..].All(static character =>
            character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static bool IsRepositoryPath(string value) =>
        value.Length > 0
        && !value.StartsWith('/')
        && !value.Contains('\\')
        && value.Split('/').All(static segment => segment is not ("" or "." or ".."));
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
