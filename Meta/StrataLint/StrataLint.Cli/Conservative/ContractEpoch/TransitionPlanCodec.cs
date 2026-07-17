using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class TransitionPlanCodec
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ImmutableArray<byte> Write(TransitionPlan plan)
    {
        ArgumentNullException.ThrowIfNull(plan);
        var material = plan switch
        {
            TransitionPlan.CustodyTransferV1 transfer => JsonSerializer.SerializeToElement(new
            {
                exact_paths = transfer.ExactPaths,
                kind = nameof(TransitionPlan.CustodyTransferV1),
                new_custodian = new
                {
                    kind = CustodianKind(transfer.NewCustodian.Kind),
                    reference = transfer.NewCustodian.Reference,
                },
                receipt = transfer.Receipt,
            }),
            TransitionPlan.AuthorityDischargeV1 discharge when discharge.RuleObligation is null =>
                JsonSerializer.SerializeToElement(new
                {
                    exact_paths = discharge.ExactPaths,
                    kind = nameof(TransitionPlan.AuthorityDischargeV1),
                    unreachability_proof_ref = discharge.UnreachabilityProofRef,
                }),
            TransitionPlan.AuthorityDischargeV1 discharge => JsonSerializer.SerializeToElement(new
            {
                kind = nameof(TransitionPlan.AuthorityDischargeV1),
                rule_obligation = discharge.RuleObligation,
                unreachability_proof_ref = discharge.UnreachabilityProofRef,
            }),
            _ => throw new InvalidOperationException("unknown transition plan case"),
        };
        return StructuredCanonicalWriter.WriteJson(material);
    }

    internal static TransitionPlan Read(ReadOnlySpan<byte> bytes)
    {
        var text = DecodeCanonical(bytes, "transition plan");
        try
        {
            using var document = JsonDocument.Parse(text);
            var root = document.RootElement;
            var kind = RequiredString(root, "kind");
            var plan = kind switch
            {
                nameof(TransitionPlan.CustodyTransferV1) => ReadTransfer(root),
                nameof(TransitionPlan.AuthorityDischargeV1) => ReadDischarge(root),
                _ => throw new FormatException($"unknown transition plan kind: {kind}"),
            };
            if (!Write(plan).AsSpan().SequenceEqual(bytes))
            {
                throw new FormatException("transition plan semantic order is not canonical");
            }

            return plan;
        }
        catch (ArgumentException exception)
        {
            throw new FormatException(exception.Message, exception);
        }
        catch (InvalidOperationException exception)
        {
            throw new FormatException("transition plan schema is invalid", exception);
        }
    }

    internal static JsonElement Element(TransitionPlan plan) =>
        JsonDocument.Parse(Write(plan).ToArray()).RootElement.Clone();

    internal static TransitionPlan ReadElement(JsonElement element)
    {
        var bytes = StructuredCanonicalWriter.WriteJson(element);
        return Read(bytes.AsSpan());
    }

    private static TransitionPlan ReadTransfer(JsonElement root)
    {
        RequireProperties(root, "exact_paths", "kind", "new_custodian", "receipt");
        var custodian = root.GetProperty("new_custodian");
        RequireProperties(custodian, "kind", "reference");
        return new TransitionPlan.CustodyTransferV1(
            StringArray(root, "exact_paths"),
            new MachineCustodian(
                ParseCustodianKind(RequiredString(custodian, "kind")),
                RequiredString(custodian, "reference")),
            RequiredString(root, "receipt"));
    }

    private static TransitionPlan ReadDischarge(JsonElement root)
    {
        var properties = root.EnumerateObject().Select(static item => item.Name).ToArray();
        if (properties.SequenceEqual(
            ["exact_paths", "kind", "unreachability_proof_ref"],
            StringComparer.Ordinal))
        {
            return new TransitionPlan.AuthorityDischargeV1(
                StringArray(root, "exact_paths"),
                null,
                RequiredString(root, "unreachability_proof_ref"));
        }

        if (properties.SequenceEqual(
            ["kind", "rule_obligation", "unreachability_proof_ref"],
            StringComparer.Ordinal))
        {
            return new TransitionPlan.AuthorityDischargeV1(
                [],
                RequiredString(root, "rule_obligation"),
                RequiredString(root, "unreachability_proof_ref"));
        }

        throw new FormatException(
            "authority discharge must contain exactly one exact_paths or rule_obligation scope");
    }

    private static string DecodeCanonical(ReadOnlySpan<byte> bytes, string context)
    {
        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException($"{context} must be strict UTF-8", exception);
        }

        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException($"{context} is not valid JSON", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException($"{context} bytes are not canonical JSON");
        }

        return text;
    }

    private static void RequireProperties(JsonElement element, params string[] expected)
    {
        if (element.ValueKind is not JsonValueKind.Object
            || !element.EnumerateObject().Select(static item => item.Name)
                .SequenceEqual(expected, StringComparer.Ordinal))
        {
            throw new FormatException("transition plan object keys are not canonical");
        }
    }

    private static string RequiredString(JsonElement root, string property)
    {
        var value = root.GetProperty(property);
        return value.ValueKind is JsonValueKind.String && value.GetString() is { Length: > 0 } text
            ? text
            : throw new FormatException($"transition plan {property} must be a non-empty string");
    }

    private static ImmutableArray<string> StringArray(JsonElement root, string property)
    {
        var value = root.GetProperty(property);
        if (value.ValueKind is not JsonValueKind.Array)
        {
            throw new FormatException($"transition plan {property} must be an array");
        }

        return value.EnumerateArray().Select(item => item.GetString()
            ?? throw new FormatException($"transition plan {property} contains a non-string"))
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
