using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal enum ContractEpochEvidenceKind
{
    Custody,
    Unreachability,
}

internal sealed class ContractEpochEvidenceReceipt
{
    private ContractEpochEvidenceReceipt(
        ContractEpochEvidenceKind kind,
        string policyRoot,
        ImmutableArray<string> exactPaths,
        string? ruleObligation,
        MachineCustodian? custodian)
    {
        Kind = kind;
        PolicyRoot = ContractEpochSyntax.PolicyRoot(policyRoot);
        ExactPaths = ContractEpochSyntax.ExactPaths(exactPaths, allowEmpty: true);
        RuleObligation = ruleObligation is null ? null : ContractEpochSyntax.RuleId(ruleObligation);
        Custodian = custodian;
        if (kind is ContractEpochEvidenceKind.Custody)
        {
            if (ExactPaths.IsEmpty || RuleObligation is not null || Custodian is null)
            {
                throw new ArgumentException("custody evidence requires exact paths and a custodian");
            }
        }
        else if (ExactPaths.IsEmpty == (RuleObligation is null) || Custodian is not null)
        {
            throw new ArgumentException(
                "unreachability evidence requires exactly one path or rule scope and no custodian");
        }

        CanonicalBytes = WriteCanonicalBytes();
        Reference = GoldenCorpusMaterializer.ContentRoot(CanonicalBytes.AsSpan());
    }

    internal ContractEpochEvidenceKind Kind { get; }

    internal string PolicyRoot { get; }

    internal ImmutableArray<string> ExactPaths { get; }

    internal string? RuleObligation { get; }

    internal MachineCustodian? Custodian { get; }

    internal ImmutableArray<byte> CanonicalBytes { get; }

    internal string Reference { get; }

    internal static ContractEpochEvidenceReceipt Custody(
        string policyRoot,
        IEnumerable<string> exactPaths,
        MachineCustodian custodian) => new(
        ContractEpochEvidenceKind.Custody,
        policyRoot,
        ContractEpochSyntax.ExactPaths(exactPaths, allowEmpty: false),
        null,
        custodian);

    internal static ContractEpochEvidenceReceipt UnreachabilityForPaths(
        string policyRoot,
        IEnumerable<string> exactPaths) => new(
        ContractEpochEvidenceKind.Unreachability,
        policyRoot,
        ContractEpochSyntax.ExactPaths(exactPaths, allowEmpty: false),
        null,
        null);

    internal static ContractEpochEvidenceReceipt UnreachabilityForRule(
        string policyRoot,
        string ruleObligation) => new(
        ContractEpochEvidenceKind.Unreachability,
        policyRoot,
        [],
        ruleObligation,
        null);

    internal static ContractEpochEvidenceReceipt Read(ReadOnlySpan<byte> bytes)
    {
        string text;
        try
        {
            text = new UTF8Encoding(false, true).GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("contract evidence must be strict UTF-8", exception);
        }

        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("contract evidence is not valid JSON", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException("contract evidence bytes are not canonical JSON");
        }

        try
        {
            using var document = JsonDocument.Parse(bytes.ToArray());
            var root = document.RootElement;
            if (!string.Equals(
                RequiredString(root, "schema"),
                "stratalint-contract-evidence-v1",
                StringComparison.Ordinal))
            {
                throw new FormatException("contract evidence schema is invalid");
            }

            var kind = RequiredString(root, "kind");
            ContractEpochEvidenceReceipt receipt;
            if (string.Equals(kind, "custody", StringComparison.Ordinal))
            {
                RequireProperties(root, "custodian", "exact_paths", "kind", "policy_root", "schema");
                var custodian = root.GetProperty("custodian");
                RequireProperties(custodian, "kind", "reference");
                receipt = Custody(
                    RequiredString(root, "policy_root"),
                    StringArray(root, "exact_paths"),
                    new MachineCustodian(
                        ParseCustodianKind(RequiredString(custodian, "kind")),
                        RequiredString(custodian, "reference")));
            }
            else if (string.Equals(kind, "unreachability", StringComparison.Ordinal)
                && root.TryGetProperty("exact_paths", out _))
            {
                RequireProperties(root, "exact_paths", "kind", "policy_root", "schema");
                receipt = UnreachabilityForPaths(
                    RequiredString(root, "policy_root"),
                    StringArray(root, "exact_paths"));
            }
            else if (string.Equals(kind, "unreachability", StringComparison.Ordinal))
            {
                RequireProperties(root, "kind", "policy_root", "rule_obligation", "schema");
                receipt = UnreachabilityForRule(
                    RequiredString(root, "policy_root"),
                    RequiredString(root, "rule_obligation"));
            }
            else
            {
                throw new FormatException($"unknown contract evidence kind: {kind}");
            }

            if (!receipt.CanonicalBytes.AsSpan().SequenceEqual(bytes))
            {
                throw new FormatException("contract evidence semantic order is not canonical");
            }

            return receipt;
        }
        catch (ArgumentException exception)
        {
            throw new FormatException(exception.Message, exception);
        }
        catch (InvalidOperationException exception)
        {
            throw new FormatException("contract evidence schema is invalid", exception);
        }
    }

    private ImmutableArray<byte> WriteCanonicalBytes()
    {
        JsonElement material;
        if (Kind is ContractEpochEvidenceKind.Custody)
        {
            material = JsonSerializer.SerializeToElement(new
            {
                custodian = new
                {
                    kind = CustodianKind(Custodian!.Kind),
                    reference = Custodian.Reference,
                },
                exact_paths = ExactPaths,
                kind = "custody",
                policy_root = PolicyRoot,
                schema = "stratalint-contract-evidence-v1",
            });
        }
        else if (RuleObligation is null)
        {
            material = JsonSerializer.SerializeToElement(new
            {
                exact_paths = ExactPaths,
                kind = "unreachability",
                policy_root = PolicyRoot,
                schema = "stratalint-contract-evidence-v1",
            });
        }
        else
        {
            material = JsonSerializer.SerializeToElement(new
            {
                kind = "unreachability",
                policy_root = PolicyRoot,
                rule_obligation = RuleObligation,
                schema = "stratalint-contract-evidence-v1",
            });
        }

        return StructuredCanonicalWriter.WriteJson(material);
    }

    private static void RequireProperties(JsonElement element, params string[] expected)
    {
        if (element.ValueKind is not JsonValueKind.Object
            || !element.EnumerateObject().Select(static item => item.Name)
                .SequenceEqual(expected, StringComparer.Ordinal))
        {
            throw new FormatException("contract evidence keys are not canonical");
        }
    }

    private static string RequiredString(JsonElement root, string property)
    {
        var value = root.GetProperty(property);
        return value.ValueKind is JsonValueKind.String && value.GetString() is { Length: > 0 } text
            ? text
            : throw new FormatException($"contract evidence {property} must be a non-empty string");
    }

    private static ImmutableArray<string> StringArray(JsonElement root, string property)
    {
        var value = root.GetProperty(property);
        if (value.ValueKind is not JsonValueKind.Array)
        {
            throw new FormatException($"contract evidence {property} must be an array");
        }

        return value.EnumerateArray().Select(item => item.GetString()
            ?? throw new FormatException($"contract evidence {property} contains a non-string"))
            .ToImmutableArray();
    }

    private static string CustodianKind(MachineCustodianKind kind) => kind switch
    {
        MachineCustodianKind.Loader => "loader",
        MachineCustodianKind.C0Anchor => "c0_anchor",
        MachineCustodianKind.RuleId => "rule_id",
        _ => throw new InvalidOperationException("unknown machine custodian kind"),
    };

    private static MachineCustodianKind ParseCustodianKind(string kind) => kind switch
    {
        "loader" => MachineCustodianKind.Loader,
        "c0_anchor" => MachineCustodianKind.C0Anchor,
        "rule_id" => MachineCustodianKind.RuleId,
        _ => throw new FormatException($"unknown machine custodian kind: {kind}"),
    };
}

internal sealed class ContractEpochEvidenceIndex
{
    private ContractEpochEvidenceIndex(
        ImmutableDictionary<string, ContractEpochEvidenceReceipt> receipts,
        ImmutableHashSet<string> existingPaths,
        ImmutableHashSet<string> c0Anchors)
    {
        Receipts = receipts;
        ExistingPaths = existingPaths;
        C0Anchors = c0Anchors;
    }

    internal static ContractEpochEvidenceIndex Empty { get; } = Create([], [], []);

    internal ImmutableDictionary<string, ContractEpochEvidenceReceipt> Receipts { get; }

    internal ImmutableHashSet<string> ExistingPaths { get; }

    internal ImmutableHashSet<string> C0Anchors { get; }

    internal static ContractEpochEvidenceIndex Create(
        IEnumerable<ContractEpochEvidenceReceipt> receipts,
        IEnumerable<string> existingPaths,
        IEnumerable<string> c0Anchors)
    {
        ArgumentNullException.ThrowIfNull(receipts);
        ArgumentNullException.ThrowIfNull(existingPaths);
        ArgumentNullException.ThrowIfNull(c0Anchors);
        var receiptMap = receipts.ToImmutableDictionary(
            static item => item.Reference,
            StringComparer.Ordinal);
        var paths = existingPaths.Select(ContractEpochSyntax.ExactPath)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var anchors = c0Anchors.Select(ContractEpochSyntax.C0Anchor)
            .ToImmutableHashSet(StringComparer.Ordinal);
        return new ContractEpochEvidenceIndex(receiptMap, paths, anchors);
    }

    internal bool CustodianExists(
        MachineCustodian custodian,
        ConservativePolicySnapshot candidate) => custodian.Kind switch
    {
        MachineCustodianKind.Loader => ExistingPaths.Contains(custodian.Reference),
        MachineCustodianKind.C0Anchor => C0Anchors.Contains(custodian.Reference),
        MachineCustodianKind.RuleId => candidate.RuleObligations.Any(item =>
            string.Equals(item.RuleId, custodian.Reference, StringComparison.Ordinal)),
        _ => false,
    };
}
