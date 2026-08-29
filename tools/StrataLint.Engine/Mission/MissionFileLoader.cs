using System.Collections.Immutable;
using System.Text.Json;
using Dunet;
using Markdig;
using Markdig.Syntax;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal enum WorthFactorId
{
    Novelty,
    DependencyReadiness,
    StructuralRealization,
    ReceiptPotential,
}

[Union(EnableImplicitConversions = false)]
internal partial record WorthFactorState
{
    public partial record Measured(decimal Value, string ReceiptRef);

    public partial record Open;
}

internal sealed record WorthFactor(WorthFactorId Id, WorthFactorState State);

internal sealed record WorthVector(ImmutableArray<WorthFactor> Factors);

internal enum WorthSelectionOrder
{
    BootstrapEligibilityOrder,
    CompleteWorthArgmax,
}

internal enum MissionNorthStarTarget
{
    TwoHearts,
}

internal enum MissionNorthStarPolicy
{
    AspirationalNotDirect,
}

internal enum MissionValue
{
    UnderstandingOverQuantity,
    HonestyOverSpeed,
    NegativeKnowledgeEqualsPositiveResults,
}

internal enum MissionProhibition
{
    SorryCountOptimization,
    TrivialLemmaAccumulation,
    CitationChasing,
}

internal sealed record MissionSelectionPolicy(
    WorthSelectionOrder OrderKind,
    string TieBreak);

internal enum FrontierEligibilityKind
{
    DeclarationReadyMathematicalOpen,
    MathematicalNotYetStated,
    Governance,
    Retired,
    Unknown,
}

internal sealed record FrontierEligibilityEntry(
    string SourceRef,
    FrontierEligibilityKind Kind,
    ImmutableArray<string> DeliveryGids = default);

internal sealed record MissionPolicy(
    MissionNorthStarTarget NorthStarTarget,
    MissionNorthStarPolicy NorthStarPolicy,
    ImmutableArray<MissionValue> ValueOrder,
    WorthVector WorthVector,
    ImmutableArray<FrontierEligibilityEntry> FrontierEligibility,
    MissionSelectionPolicy Selection,
    ImmutableArray<MissionProhibition> Prohibitions);

internal enum MissionLoadErrorCode
{
    Missing,
    InvalidFormat,
    InvalidSchema,
    InvalidWorthVector,
    InvalidWorthState,
    InvalidSelection,
}

internal sealed record MissionLoadError(MissionLoadErrorCode Code, string Message);

[Union(EnableImplicitConversions = false)]
internal partial record MissionLoadOutcome
{
    public partial record Loaded(MissionPolicy Policy);

    public partial record Invalid(MissionLoadError Error);
}

internal static partial class MissionFileLoader
{
    internal const string RelativePath = "docs/MISSION.md";

    private const string Schema = "trureturing-mission-v1";
    private const string MissionFence = "mission-v1";
    private const string BootstrapOrder = "bootstrap eligibility order";
    private const string CompleteArgmax = "complete worth argmax";
    private const string CanonicalTieBreak = "canonical candidate id";
    private const string CanonicalNorthStarTarget = "two hearts";
    private const string CanonicalNorthStarPolicy = "aspirational-not-direct";

    private static readonly MarkdownPipeline MarkdownPipeline = new MarkdownPipelineBuilder()
        .UsePreciseSourceLocation()
        .Build();

    private static readonly ImmutableArray<(string Name, WorthFactorId Id)> FactorOrder =
    [
        ("novelty", WorthFactorId.Novelty),
        ("dependency_readiness", WorthFactorId.DependencyReadiness),
        ("structural_realization", WorthFactorId.StructuralRealization),
        ("receipt_potential", WorthFactorId.ReceiptPotential),
    ];

    private static readonly ImmutableArray<(string Name, MissionValue Value)> CanonicalValueOrder =
    [
        ("understanding-over-quantity", MissionValue.UnderstandingOverQuantity),
        ("honesty-over-speed", MissionValue.HonestyOverSpeed),
        ("negative-knowledge-equals-positive-results", MissionValue.NegativeKnowledgeEqualsPositiveResults),
    ];

    private static readonly ImmutableArray<(string Name, MissionProhibition Value)> CanonicalProhibitions =
    [
        ("sorry-count optimization", MissionProhibition.SorryCountOptimization),
        ("trivial-lemma accumulation", MissionProhibition.TrivialLemmaAccumulation),
        ("citation chasing", MissionProhibition.CitationChasing),
    ];

    internal static MissionLoadOutcome Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        if (!snapshot.TryGetFile(RelativePath, out var mission))
        {
            return Invalid(
                MissionLoadErrorCode.Missing,
                $"MISSION file is missing: {RelativePath}");
        }

        if (mission.IsOpaque || mission.HasBom || mission.HasCarriageReturn
            || !mission.Text.EndsWith('\n'))
        {
            return Invalid(
                MissionLoadErrorCode.InvalidFormat,
                "MISSION must be strict UTF-8 without BOM, use LF line endings, and end with LF");
        }

        try
        {
            var policy = ParseMission(mission.Text);
            ValidateFrontierEligibility(snapshot, policy.FrontierEligibility);
            return new MissionLoadOutcome.Loaded(policy);
        }
        catch (MissionContractException exception)
        {
            return Invalid(exception.Code, exception.Message);
        }
        catch (JsonException exception)
        {
            return Invalid(MissionLoadErrorCode.InvalidFormat, exception.Message);
        }
        catch (FormatException exception)
        {
            return Invalid(MissionLoadErrorCode.InvalidFormat, exception.Message);
        }
    }

    internal static MissionLoadOutcome LoadRepository(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        try
        {
            return SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(repositoryRoot)) switch
            {
                SnapshotDecodeOutcome.Decoded decoded => Load(decoded.Snapshot),
                SnapshotDecodeOutcome.InfrastructureFailure failure =>
                    Invalid(MissionLoadErrorCode.InvalidFormat, failure.Message),
            };
        }
        catch (Exception exception) when (
            exception is IOException or InvalidOperationException or UnauthorizedAccessException)
        {
            return Invalid(MissionLoadErrorCode.InvalidFormat, exception.Message);
        }
    }

    internal static byte[] CanonicalBytes(MissionPolicy policy)
    {
        ArgumentNullException.ThrowIfNull(policy);
        var factors = policy.WorthVector.Factors.Select(static factor => new
        {
            factor = FactorName(factor.Id),
            state = factor.State switch
            {
                WorthFactorState.Open => (object)new
                {
                    state = "open",
                },
                WorthFactorState.Measured measured => new
                {
                    receipt_ref = measured.ReceiptRef,
                    state = "measured",
                    value = measured.Value,
                },
                _ => throw new InvalidOperationException("Unknown worth factor state."),
            },
        });
        var material = JsonSerializer.SerializeToElement(new
        {
            north_star = new
            {
                policy = NorthStarPolicyName(policy.NorthStarPolicy),
                target = NorthStarTargetName(policy.NorthStarTarget),
            },
            prohibitions = policy.Prohibitions
                .Select(ProhibitionName)
                .ToImmutableArray(),
            frontier_eligibility = policy.FrontierEligibility.Select(static entry =>
                entry.Kind is FrontierEligibilityKind.Retired
                    ? (object)new
                    {
                        delivery_gids = entry.DeliveryGids,
                        kind = FrontierEligibilityKindName(entry.Kind),
                        source_ref = entry.SourceRef,
                    }
                    : new
                    {
                        kind = FrontierEligibilityKindName(entry.Kind),
                        source_ref = entry.SourceRef,
                    }).ToImmutableArray(),
            schema = Schema,
            selection = new
            {
                order_kind = SelectionName(policy.Selection.OrderKind),
                tie_break = policy.Selection.TieBreak,
            },
            value_order = policy.ValueOrder
                .Select(ValueName)
                .ToImmutableArray(),
            worth_vector = factors,
        });
        return StructuredCanonicalWriter.WriteJson(material).ToArray();
    }

    // Baseline Frontier ownership is an independent typed projection. It deliberately does not
    // inspect the baseline worth vector, whose schema may predate the current payload-free open
    // state. Current candidates continue to use Load and therefore the complete current schema.
    internal static bool TryLoadFrontierEligibility(
        RepositorySnapshot snapshot,
        out ImmutableArray<FrontierEligibilityEntry> entries,
        out string? error)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        entries = [];
        error = null;
        if (!snapshot.TryGetFile(RelativePath, out var mission))
        {
            error = $"MISSION file is missing: {RelativePath}";
            return false;
        }

        if (mission.IsOpaque || mission.HasBom || mission.HasCarriageReturn
            || !mission.Text.EndsWith('\n'))
        {
            error = "MISSION must be strict UTF-8 without BOM, use LF line endings, and end with LF";
            return false;
        }

        try
        {
            var fences = Markdown.Parse(mission.Text, MarkdownPipeline)
                .Descendants<FencedCodeBlock>()
                .ToArray();
            if (fences is not [var fence]
                || !string.Equals(fence.Info?.ToString(), MissionFence, StringComparison.Ordinal))
            {
                throw Error(
                    MissionLoadErrorCode.InvalidFormat,
                    $"MISSION must contain exactly one {MissionFence} fenced block");
            }

            using var document = JsonDocument.Parse(fence.Lines.ToString());
            var root = RequireObject(document.RootElement, MissionLoadErrorCode.InvalidSchema, "root");
            entries = root.TryGetProperty("frontier_eligibility", out var frontier)
                ? ParseFrontierEligibility(frontier)
                : [];
            ValidateFrontierEligibility(snapshot, entries);
            return true;
        }
        catch (MissionContractException exception)
        {
            error = exception.Message;
            return false;
        }
        catch (JsonException exception)
        {
            error = exception.Message;
            return false;
        }
        catch (FormatException exception)
        {
            error = exception.Message;
            return false;
        }
    }

    private static MissionPolicy ParseMission(string source)
    {
        var fences = Markdown.Parse(source, MarkdownPipeline)
            .Descendants<FencedCodeBlock>()
            .ToArray();
        if (fences is not [var fence]
            || !string.Equals(fence.Info?.ToString(), MissionFence, StringComparison.Ordinal))
        {
            throw Error(
                MissionLoadErrorCode.InvalidFormat,
                $"MISSION must contain exactly one {MissionFence} fenced block");
        }

        using var document = JsonDocument.Parse(fence.Lines.ToString());
        var root = RequireObject(document.RootElement, MissionLoadErrorCode.InvalidSchema, "root");
        var hasFrontierEligibility = root.TryGetProperty("frontier_eligibility", out var frontierValue);
        RequireExactKeys(
            root,
            hasFrontierEligibility
                ? [
                    "schema", "north_star", "value_order", "worth_vector",
                    "frontier_eligibility", "selection", "prohibitions",
                ]
                : ["schema", "north_star", "value_order", "worth_vector", "selection", "prohibitions"],
            MissionLoadErrorCode.InvalidSchema,
            "root");
        if (!string.Equals(
                RequireString(root, "schema", MissionLoadErrorCode.InvalidSchema),
                Schema,
                StringComparison.Ordinal))
        {
            throw Error(MissionLoadErrorCode.InvalidSchema, $"schema must be {Schema}");
        }

        var northStar = RequireObject(
            RequireProperty(root, "north_star", MissionLoadErrorCode.InvalidSchema),
            MissionLoadErrorCode.InvalidSchema,
            "north_star");
        RequireExactKeys(
            northStar,
            ["target", "policy"],
            MissionLoadErrorCode.InvalidSchema,
            "north_star");

        var northStarTarget = ParseNorthStarTarget(northStar);
        var northStarPolicy = ParseNorthStarPolicy(northStar);
        var valueOrder = RequireCanonicalArray(
            RequireProperty(root, "value_order", MissionLoadErrorCode.InvalidSchema),
            MissionLoadErrorCode.InvalidSchema,
            "value_order",
            CanonicalValueOrder);
        var prohibitions = RequireCanonicalArray(
            RequireProperty(root, "prohibitions", MissionLoadErrorCode.InvalidSchema),
            MissionLoadErrorCode.InvalidSchema,
            "prohibitions",
            CanonicalProhibitions);
        var worthVector = ParseWorthVector(RequireProperty(
            root,
            "worth_vector",
            MissionLoadErrorCode.InvalidWorthVector));
        RejectP0MeasuredFactors(worthVector);
        var frontierEligibility = hasFrontierEligibility
            ? ParseFrontierEligibility(frontierValue)
            : [];
        var selection = ParseSelection(
            RequireProperty(root, "selection", MissionLoadErrorCode.InvalidSelection),
            worthVector);

        return new MissionPolicy(
            northStarTarget,
            northStarPolicy,
            valueOrder,
            worthVector,
            frontierEligibility,
            selection,
            prohibitions);
    }

    private static MissionNorthStarTarget ParseNorthStarTarget(JsonElement northStar) =>
        RequireString(northStar, "target", MissionLoadErrorCode.InvalidSchema) switch
        {
            CanonicalNorthStarTarget => MissionNorthStarTarget.TwoHearts,
            _ => throw Error(
                MissionLoadErrorCode.InvalidSchema,
                $"north_star.target must be {CanonicalNorthStarTarget}"),
        };

    private static MissionNorthStarPolicy ParseNorthStarPolicy(JsonElement northStar) =>
        RequireString(northStar, "policy", MissionLoadErrorCode.InvalidSchema) switch
        {
            CanonicalNorthStarPolicy => MissionNorthStarPolicy.AspirationalNotDirect,
            _ => throw Error(
                MissionLoadErrorCode.InvalidSchema,
                $"north_star.policy must be {CanonicalNorthStarPolicy}"),
        };

    private static WorthVector ParseWorthVector(JsonElement value)
    {
        var vector = RequireObject(value, MissionLoadErrorCode.InvalidWorthVector, "worth_vector");
        RequireExactKeys(
            vector,
            FactorOrder.Select(static factor => factor.Name),
            MissionLoadErrorCode.InvalidWorthVector,
            "worth_vector");
        return new WorthVector(FactorOrder
            .Select(factor => new WorthFactor(
                factor.Id,
                ParseWorthState(RequireProperty(
                    vector,
                    factor.Name,
                    MissionLoadErrorCode.InvalidWorthVector), factor.Name)))
            .ToImmutableArray());
    }

    private static WorthFactorState ParseWorthState(JsonElement value, string factorName)
    {
        var state = RequireObject(
            value,
            MissionLoadErrorCode.InvalidWorthState,
            $"worth_vector.{factorName}");
        var stateName = RequireString(state, "state", MissionLoadErrorCode.InvalidWorthState);
        if (string.Equals(stateName, "open", StringComparison.Ordinal))
        {
            RequireExactKeys(
                state,
                ["state"],
                MissionLoadErrorCode.InvalidWorthState,
                $"worth_vector.{factorName}");

            return new WorthFactorState.Open();
        }

        if (string.Equals(stateName, "measured", StringComparison.Ordinal))
        {
            RequireExactKeys(
                state,
                ["state", "value", "receipt_ref"],
                MissionLoadErrorCode.InvalidWorthState,
                $"worth_vector.{factorName}");
            var number = RequireProperty(state, "value", MissionLoadErrorCode.InvalidWorthState);
            if (number.ValueKind is not JsonValueKind.Number || !number.TryGetDecimal(out var measured))
            {
                throw Error(
                    MissionLoadErrorCode.InvalidWorthState,
                    $"worth_vector.{factorName}.value must be an exact decimal number");
            }

            return new WorthFactorState.Measured(
                measured,
                RequireString(state, "receipt_ref", MissionLoadErrorCode.InvalidWorthState));
        }

        throw Error(
            MissionLoadErrorCode.InvalidWorthState,
            $"worth_vector.{factorName}.state must be open or measured");
    }

    private static void RejectP0MeasuredFactors(WorthVector vector)
    {
        foreach (var factor in vector.Factors
                     .Where(static factor => factor.State is WorthFactorState.Measured))
        {
            throw Error(
                MissionLoadErrorCode.InvalidWorthState,
                $"worth_vector.{FactorName(factor.Id)} measured is fail-closed in P0 "
                + "until a machine-replayable measurement receipt contract and resolver are implemented");
        }
    }

    private static MissionSelectionPolicy ParseSelection(JsonElement value, WorthVector vector)
    {
        var selection = RequireObject(value, MissionLoadErrorCode.InvalidSelection, "selection");
        RequireExactKeys(
            selection,
            ["order_kind", "tie_break"],
            MissionLoadErrorCode.InvalidSelection,
            "selection");
        var orderName = RequireString(selection, "order_kind", MissionLoadErrorCode.InvalidSelection);
        var order = orderName switch
        {
            BootstrapOrder => WorthSelectionOrder.BootstrapEligibilityOrder,
            CompleteArgmax => WorthSelectionOrder.CompleteWorthArgmax,
            _ => throw Error(
                MissionLoadErrorCode.InvalidSelection,
                $"selection.order_kind must be {BootstrapOrder} or {CompleteArgmax}"),
        };
        var tieBreak = RequireString(selection, "tie_break", MissionLoadErrorCode.InvalidSelection);
        if (!string.Equals(tieBreak, CanonicalTieBreak, StringComparison.Ordinal))
        {
            throw Error(
                MissionLoadErrorCode.InvalidSelection,
                $"selection.tie_break must be {CanonicalTieBreak}");
        }

        if (vector.Factors.Any(static factor => factor.State is WorthFactorState.Open)
            && order is not WorthSelectionOrder.BootstrapEligibilityOrder)
        {
            throw Error(
                MissionLoadErrorCode.InvalidSelection,
                "an open worth factor forbids a complete worth score or argmax");
        }

        return new MissionSelectionPolicy(order, tieBreak);
    }


    private static JsonElement RequireObject(
        JsonElement value,
        MissionLoadErrorCode code,
        string name)
    {
        if (value.ValueKind is not JsonValueKind.Object)
        {
            throw Error(code, $"{name} must be an object");
        }

        return value;
    }

    private static JsonElement RequireProperty(
        JsonElement value,
        string name,
        MissionLoadErrorCode code)
    {
        if (!value.TryGetProperty(name, out var property))
        {
            throw Error(code, $"missing required property: {name}");
        }

        return property;
    }

    private static string RequireString(
        JsonElement value,
        string name,
        MissionLoadErrorCode code)
    {
        var property = RequireProperty(value, name, code);
        if (property.ValueKind is not JsonValueKind.String
            || string.IsNullOrWhiteSpace(property.GetString()))
        {
            throw Error(code, $"{name} must be a non-empty string");
        }

        return property.GetString()!;
    }

    private static ImmutableArray<string> RequireStringArray(
        JsonElement value,
        MissionLoadErrorCode code,
        string name)
    {
        if (value.ValueKind is not JsonValueKind.Array)
        {
            throw Error(code, $"{name} must be an array");
        }

        var result = ImmutableArray.CreateBuilder<string>();
        foreach (var item in value.EnumerateArray())
        {
            if (item.ValueKind is not JsonValueKind.String
                || string.IsNullOrWhiteSpace(item.GetString()))
            {
                throw Error(code, $"{name} items must be non-empty strings");
            }

            result.Add(item.GetString()!);
        }

        if (result.Count == 0)
        {
            throw Error(code, $"{name} must not be empty");
        }

        return result.ToImmutable();
    }

    private static ImmutableArray<T> RequireCanonicalArray<T>(
        JsonElement value,
        MissionLoadErrorCode code,
        string name,
        ImmutableArray<(string Name, T Value)> canonical)
        where T : struct, Enum
    {
        var actual = RequireStringArray(value, code, name);
        if (!actual.SequenceEqual(
                canonical.Select(static item => item.Name),
                StringComparer.Ordinal))
        {
            throw Error(
                code,
                $"{name} must exactly match the canonical ordered values");
        }

        return canonical.Select(static item => item.Value).ToImmutableArray();
    }

    private static void RequireExactKeys(
        JsonElement value,
        IEnumerable<string> expected,
        MissionLoadErrorCode code,
        string name)
    {
        var actual = value.EnumerateObject().Select(static property => property.Name).ToArray();
        var required = expected.ToArray();
        if (actual.Length != required.Length
            || actual.Distinct(StringComparer.Ordinal).Count() != actual.Length
            || !actual.ToHashSet(StringComparer.Ordinal).SetEquals(required))
        {
            throw Error(code, $"{name} has unknown, duplicate, or missing properties");
        }
    }

    private static string FactorName(WorthFactorId factor) => factor switch
    {
        WorthFactorId.Novelty => "novelty",
        WorthFactorId.DependencyReadiness => "dependency_readiness",
        WorthFactorId.StructuralRealization => "structural_realization",
        WorthFactorId.ReceiptPotential => "receipt_potential",
        _ => throw new InvalidOperationException("Unknown worth factor."),
    };

    private static string NorthStarTargetName(MissionNorthStarTarget target) => target switch
    {
        MissionNorthStarTarget.TwoHearts => CanonicalNorthStarTarget,
        _ => throw new InvalidOperationException("Unknown mission north-star target."),
    };

    private static string NorthStarPolicyName(MissionNorthStarPolicy policy) => policy switch
    {
        MissionNorthStarPolicy.AspirationalNotDirect => CanonicalNorthStarPolicy,
        _ => throw new InvalidOperationException("Unknown mission north-star policy."),
    };

    private static string ValueName(MissionValue value) => value switch
    {
        MissionValue.UnderstandingOverQuantity => "understanding-over-quantity",
        MissionValue.HonestyOverSpeed => "honesty-over-speed",
        MissionValue.NegativeKnowledgeEqualsPositiveResults =>
            "negative-knowledge-equals-positive-results",
        _ => throw new InvalidOperationException("Unknown mission value."),
    };

    private static string ProhibitionName(MissionProhibition prohibition) => prohibition switch
    {
        MissionProhibition.SorryCountOptimization => "sorry-count optimization",
        MissionProhibition.TrivialLemmaAccumulation => "trivial-lemma accumulation",
        MissionProhibition.CitationChasing => "citation chasing",
        _ => throw new InvalidOperationException("Unknown mission prohibition."),
    };

    private static string FrontierEligibilityKindName(FrontierEligibilityKind kind) => kind switch
    {
        FrontierEligibilityKind.DeclarationReadyMathematicalOpen =>
            "declaration-ready-mathematical-open",
        FrontierEligibilityKind.MathematicalNotYetStated => "mathematical-not-yet-stated",
        FrontierEligibilityKind.Governance => "governance",
        FrontierEligibilityKind.Retired => "retired",
        FrontierEligibilityKind.Unknown => "unknown",
        _ => throw new InvalidOperationException("Unknown Frontier eligibility kind."),
    };

    internal static string SelectionName(WorthSelectionOrder order) => order switch
    {
        WorthSelectionOrder.BootstrapEligibilityOrder => BootstrapOrder,
        WorthSelectionOrder.CompleteWorthArgmax => CompleteArgmax,
        _ => throw new InvalidOperationException("Unknown worth selection order."),
    };

    private static MissionLoadOutcome.Invalid Invalid(MissionLoadErrorCode code, string message) =>
        new(new MissionLoadError(code, message));

    private static MissionContractException Error(MissionLoadErrorCode code, string message) =>
        new(code, message);

    private sealed class MissionContractException(MissionLoadErrorCode code, string message)
        : FormatException(message)
    {
        internal MissionLoadErrorCode Code { get; } = code;
    }
}
