using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record RuleObligationAtom(
    string RuleId,
    string AdmissionEffect,
    string DescriptorRoot);

internal sealed class ConservativePolicySnapshot
{
    private const string MarkerPrefix = "CONTRACT-POLICY-V1/";

    private ConservativePolicySnapshot(
        ImmutableArray<ProtectionMatcher> protectionMatchers,
        ImmutableArray<string> exactExclusions,
        ImmutableArray<string> legacyPrefixExclusions,
        ImmutableArray<RuleObligationAtom> ruleObligations)
    {
        ProtectionMatchers = protectionMatchers
            .OrderBy(static item => item.Id, StringComparer.Ordinal)
            .ToImmutableArray();
        ExactExclusions = exactExclusions.Order(StringComparer.Ordinal).ToImmutableArray();
        LegacyPrefixExclusions = legacyPrefixExclusions.Order(StringComparer.Ordinal).ToImmutableArray();
        RuleObligations = ruleObligations
            .OrderBy(static item => item.RuleId, StringComparer.Ordinal)
            .ToImmutableArray();
        CanonicalBytes = WriteCanonicalBytes();
        Root = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(CanonicalBytes.AsSpan()));
    }

    internal ImmutableArray<ProtectionMatcher> ProtectionMatchers { get; }

    internal ImmutableArray<string> ExactExclusions { get; }

    internal ImmutableArray<string> LegacyPrefixExclusions { get; }

    internal ImmutableArray<RuleObligationAtom> RuleObligations { get; }

    internal ImmutableArray<byte> CanonicalBytes { get; }

    internal string Root { get; }

    internal string Marker => MarkerPrefix
        + Root["sha256:".Length..]
        + "/"
        + Base64UrlEncode(CanonicalBytes.AsSpan());

    internal static bool IsMarker(string value) =>
        value.StartsWith(MarkerPrefix, StringComparison.Ordinal);

    internal static ConservativePolicySnapshot FromMarker(string marker)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(marker);
        if (!IsMarker(marker)) throw new FormatException("contract policy marker prefix is invalid");
        var payload = marker[MarkerPrefix.Length..];
        var separator = payload.IndexOf('/');
        if (separator != 64
            || payload[..separator].Any(static character =>
                character is not (>= '0' and <= '9') and not (>= 'a' and <= 'f')))
        {
            throw new FormatException("contract policy marker root is invalid");
        }

        var expectedRoot = "sha256:" + payload[..separator];
        var bytes = Base64UrlDecode(payload[(separator + 1)..]);
        var actualRoot = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));
        if (!string.Equals(expectedRoot, actualRoot, StringComparison.Ordinal))
        {
            throw new FormatException("contract policy marker root does not match its bytes");
        }

        string text;
        try
        {
            text = new UTF8Encoding(false, true).GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("contract policy marker must be strict UTF-8", exception);
        }

        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("contract policy marker is not valid JSON", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException("contract policy marker bytes are not canonical JSON");
        }

        try
        {
            using var document = JsonDocument.Parse(bytes);
            var root = document.RootElement;
            RequireProperties(
                root,
                "exact_exclusions",
                "legacy_prefix_exclusions",
                "protection_matchers",
                "rule_obligations",
                "schema");
            if (!string.Equals(
                RequiredString(root, "schema"),
                "stratalint-contract-policy-v1",
                StringComparison.Ordinal))
            {
                throw new FormatException("contract policy schema is invalid");
            }

            var exactExclusions = StringArray(root, "exact_exclusions");
            var legacyExclusions = StringArray(root, "legacy_prefix_exclusions");
            var matchers = root.GetProperty("protection_matchers")
                .EnumerateArray()
                .Select(ParseMatcher)
                .ToImmutableArray();
            var rules = root.GetProperty("rule_obligations")
                .EnumerateArray()
                .Select(ParseRuleObligation)
                .ToImmutableArray();
            RequireSortedUnique(exactExclusions, "exact exclusions");
            RequireSortedUnique(legacyExclusions, "legacy prefix exclusions");
            RequireSortedUnique(matchers.Select(static item => item.Id), "protection matcher ids");
            RequireSortedUnique(rules.Select(static item => item.RuleId), "rule obligations");
            var parsed = new ConservativePolicySnapshot(
                matchers,
                exactExclusions,
                legacyExclusions,
                rules);
            if (!string.Equals(parsed.Root, expectedRoot, StringComparison.Ordinal)
                || !parsed.CanonicalBytes.AsSpan().SequenceEqual(bytes))
            {
                throw new FormatException("contract policy marker is not in canonical semantic order");
            }

            return parsed;
        }
        catch (InvalidOperationException exception)
        {
            throw new FormatException("contract policy marker schema is invalid", exception);
        }
    }

    internal static ConservativePolicySnapshot Current()
    {
        var obligations = RuleCatalog.Default.Descriptors
            .Where(static item => item.Lifecycle is RuleLifecycle.Active)
            .Select(static item => new RuleObligationAtom(
                item.Id.Value,
                item.AdmissionEffect.ToString(),
                DescriptorRoot(item)))
            .ToImmutableArray();
        return new ConservativePolicySnapshot(
            BootstrapProtectionPolicy.Matchers,
            BootstrapProtectionPolicy.ExactExclusions,
            BootstrapProtectionPolicy.LegacyPrefixExclusions,
            obligations);
    }

    internal ConservativePolicySnapshot WithExactExclusions(IEnumerable<string> paths)
    {
        ArgumentNullException.ThrowIfNull(paths);
        var exclusions = paths.Select(RequireExactPath).ToImmutableArray();
        return new ConservativePolicySnapshot(
            ProtectionMatchers,
            exclusions,
            LegacyPrefixExclusions,
            RuleObligations);
    }

    internal ConservativePolicySnapshot WithoutProtectionMatcher(string id)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(id);
        return new ConservativePolicySnapshot(
            ProtectionMatchers.Where(item => !string.Equals(item.Id, id, StringComparison.Ordinal))
                .ToImmutableArray(),
            ExactExclusions,
            LegacyPrefixExclusions,
            RuleObligations);
    }

    internal ConservativePolicySnapshot WithoutRuleObligation(string ruleId)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(ruleId);
        return new ConservativePolicySnapshot(
            ProtectionMatchers,
            ExactExclusions,
            LegacyPrefixExclusions,
            RuleObligations.Where(item =>
                    !string.Equals(item.RuleId, ruleId, StringComparison.Ordinal))
                .ToImmutableArray());
    }

    internal ConservativePolicySnapshot WithRuleObligations(IEnumerable<string> ruleIds)
    {
        ArgumentNullException.ThrowIfNull(ruleIds);
        var requested = ruleIds.ToHashSet(StringComparer.Ordinal);
        var obligations = RuleObligations.Where(item => requested.Remove(item.RuleId))
            .ToImmutableArray();
        if (requested.Count != 0)
        {
            throw new ArgumentException(
                "policy references unknown active rules: "
                + string.Join(',', requested.Order(StringComparer.Ordinal)));
        }

        return new ConservativePolicySnapshot(
            ProtectionMatchers,
            ExactExclusions,
            LegacyPrefixExclusions,
            obligations);
    }

    internal bool IsProtected(string path) => BootstrapProtectionPolicy.IsProtected(
        path,
        ProtectionMatchers,
        ExactExclusions,
        LegacyPrefixExclusions);

    private ImmutableArray<byte> WriteCanonicalBytes()
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            exact_exclusions = ExactExclusions,
            legacy_prefix_exclusions = LegacyPrefixExclusions,
            protection_matchers = ProtectionMatchers.Select(static item => new
            {
                comparison = item.Comparison.ToString(),
                id = item.Id,
                kind = item.Kind.ToString(),
                pattern = item.Pattern,
            }),
            rule_obligations = RuleObligations.Select(static item => new
            {
                admission_effect = item.AdmissionEffect,
                descriptor_root = item.DescriptorRoot,
                rule_id = item.RuleId,
            }),
            schema = "stratalint-contract-policy-v1",
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    private static string DescriptorRoot(RuleDescriptor descriptor)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            admission_effect = descriptor.AdmissionEffect.ToString(),
            category = descriptor.Category,
            deferred_case = descriptor.DeferredCase?.Value,
            display_severity = descriptor.DisplaySeverity.ToString(),
            id = descriptor.Id.Value,
            lifecycle = descriptor.Lifecycle.ToString(),
            title = descriptor.Title,
        });
        var bytes = StructuredCanonicalWriter.WriteJson(material);
        return "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes.AsSpan()));
    }

    private static string RequireExactPath(string raw)
    {
        if (!RepoPath.TryCreate(raw, out var path)
            || raw.IndexOfAny(['*', '?', '[', ']', '{', '}']) >= 0)
        {
            throw new ArgumentException($"contract policy exclusion is not an exact path: {raw}");
        }

        return path.Value;
    }

    private static ProtectionMatcher ParseMatcher(JsonElement item)
    {
        RequireProperties(item, "comparison", "id", "kind", "pattern");
        if (!Enum.TryParse<ProtectionComparison>(
                RequiredString(item, "comparison"),
                ignoreCase: false,
                out var comparison)
            || !Enum.TryParse<ProtectionMatchKind>(
                RequiredString(item, "kind"),
                ignoreCase: false,
                out var kind))
        {
            throw new FormatException("contract policy matcher enum is invalid");
        }

        return new ProtectionMatcher(
            RequiredString(item, "id"),
            kind,
            RequiredString(item, "pattern"),
            comparison);
    }

    private static RuleObligationAtom ParseRuleObligation(JsonElement item)
    {
        RequireProperties(item, "admission_effect", "descriptor_root", "rule_id");
        return new RuleObligationAtom(
            RequiredString(item, "rule_id"),
            RequiredString(item, "admission_effect"),
            RequiredString(item, "descriptor_root"));
    }

    private static ImmutableArray<string> StringArray(JsonElement root, string property)
    {
        var values = root.GetProperty(property);
        if (values.ValueKind is not JsonValueKind.Array)
        {
            throw new FormatException($"contract policy {property} must be an array");
        }

        return values.EnumerateArray().Select(item => item.GetString()
            ?? throw new FormatException($"contract policy {property} contains a non-string"))
            .ToImmutableArray();
    }

    private static string RequiredString(JsonElement root, string property)
    {
        var value = root.GetProperty(property);
        if (value.ValueKind is not JsonValueKind.String
            || value.GetString() is not { Length: > 0 } text)
        {
            throw new FormatException($"contract policy {property} must be a non-empty string");
        }

        return text;
    }

    private static void RequireProperties(JsonElement element, params string[] expected)
    {
        if (element.ValueKind is not JsonValueKind.Object
            || !element.EnumerateObject().Select(static item => item.Name)
                .SequenceEqual(expected, StringComparer.Ordinal))
        {
            throw new FormatException("contract policy object keys are not canonical");
        }
    }

    private static void RequireSortedUnique(IEnumerable<string> values, string context)
    {
        string? previous = null;
        foreach (var value in values)
        {
            if (string.IsNullOrWhiteSpace(value)
                || previous is not null && string.CompareOrdinal(previous, value) >= 0)
            {
                throw new FormatException($"contract policy {context} must be sorted and unique");
            }

            previous = value;
        }
    }

    private static string Base64UrlEncode(ReadOnlySpan<byte> bytes) =>
        Convert.ToBase64String(bytes).TrimEnd('=').Replace('+', '-').Replace('/', '_');

    private static byte[] Base64UrlDecode(string value)
    {
        if (value.Length == 0 || value.Any(static character =>
            !char.IsAsciiLetterOrDigit(character) && character is not '-' and not '_'))
        {
            throw new FormatException("contract policy marker payload is not base64url");
        }

        var padded = value.Replace('-', '+').Replace('_', '/');
        padded += (padded.Length % 4) switch
        {
            0 => string.Empty,
            2 => "==",
            3 => "=",
            _ => throw new FormatException("contract policy marker payload length is invalid"),
        };
        try
        {
            return Convert.FromBase64String(padded);
        }
        catch (FormatException exception)
        {
            throw new FormatException("contract policy marker payload is not base64url", exception);
        }
    }
}
