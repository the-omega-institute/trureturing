using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal abstract record ContractEpochEvent
{
    private ContractEpochEvent() { }

    internal sealed record Register : ContractEpochEvent
    {
        internal Register(
            string planId,
            string baselineTreeOid,
            string prePolicyRoot,
            string postPolicyRoot,
            TransitionPlan plan)
        {
            PlanId = ContractEpochSyntax.PlanId(planId);
            BaselineTreeOid = ContractEpochSyntax.TreeOid(baselineTreeOid);
            PrePolicyRoot = ContractEpochSyntax.PolicyRoot(prePolicyRoot);
            PostPolicyRoot = ContractEpochSyntax.PolicyRoot(postPolicyRoot);
            Plan = plan ?? throw new ArgumentNullException(nameof(plan));
            PlanRoot = GoldenCorpusMaterializer.ContentRoot(TransitionPlanCodec.Write(plan).AsSpan());
        }

        internal string PlanId { get; }

        internal string BaselineTreeOid { get; }

        internal string PrePolicyRoot { get; }

        internal string PostPolicyRoot { get; }

        internal TransitionPlan Plan { get; }

        internal string PlanRoot { get; }
    }

    internal sealed record Consume : ContractEpochEvent
    {
        internal Consume(string planId) => PlanId = ContractEpochSyntax.PlanId(planId);

        internal string PlanId { get; }
    }
}

internal sealed class ContractEpochLedger
{
    private ContractEpochLedger(ImmutableArray<ContractEpochEvent> events, ImmutableArray<byte> bytes)
    {
        Events = events;
        CanonicalBytes = bytes;
        Root = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes.AsSpan()));
    }

    internal static ContractEpochLedger Empty { get; } = new([], []);

    internal ImmutableArray<ContractEpochEvent> Events { get; }

    internal ImmutableArray<byte> CanonicalBytes { get; }

    internal string Root { get; }

    internal static ContractEpochLedger Create(
        ImmutableArray<ContractEpochEvent> events,
        ImmutableArray<byte> bytes) => new(events, bytes);

    internal static ContractEpochLedgerDelta Compare(
        ContractEpochLedger baseline,
        ContractEpochLedger candidate)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidate);
        if (candidate.CanonicalBytes.Length < baseline.CanonicalBytes.Length
            || !candidate.CanonicalBytes.AsSpan()[..baseline.CanonicalBytes.Length]
                .SequenceEqual(baseline.CanonicalBytes.AsSpan()))
        {
            throw new InvalidOperationException(
                "candidate contract epoch ledger is not an append-only extension of the exact base ledger");
        }

        var registrations = baseline.Events
            .OfType<ContractEpochEvent.Register>()
            .ToDictionary(static item => item.PlanId, StringComparer.Ordinal);
        var consumed = baseline.Events
            .OfType<ContractEpochEvent.Consume>()
            .Select(static item => item.PlanId)
            .ToHashSet(StringComparer.Ordinal);
        var newRegistrations = candidate.Events.Skip(baseline.Events.Length)
            .OfType<ContractEpochEvent.Register>()
            .ToImmutableArray();
        var eligible = ImmutableArray.CreateBuilder<ContractEpochEvent.Register>();
        var ineligible = ImmutableArray.CreateBuilder<string>();
        foreach (var consumption in candidate.Events.Skip(baseline.Events.Length)
            .OfType<ContractEpochEvent.Consume>())
        {
            if (registrations.TryGetValue(consumption.PlanId, out var registration)
                && !consumed.Contains(consumption.PlanId))
            {
                eligible.Add(registration);
            }
            else
            {
                ineligible.Add(consumption.PlanId);
            }
        }

        return new ContractEpochLedgerDelta(
            newRegistrations,
            eligible.ToImmutable(),
            ineligible.Order(StringComparer.Ordinal).ToImmutableArray());
    }
}

internal sealed record ContractEpochLedgerDelta(
    ImmutableArray<ContractEpochEvent.Register> NewRegistrations,
    ImmutableArray<ContractEpochEvent.Register> EligibleConsumptions,
    ImmutableArray<string> IneligibleConsumptions);

internal static class ContractEpochLedgerCodec
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ImmutableArray<byte> Write(IEnumerable<ContractEpochEvent> events)
    {
        ArgumentNullException.ThrowIfNull(events);
        using var stream = new MemoryStream();
        foreach (var item in events)
        {
            var bytes = StructuredCanonicalWriter.WriteJson(EventElement(item));
            stream.Write(bytes.AsSpan());
        }

        return ImmutableArray.CreateRange(stream.ToArray());
    }

    internal static ContractEpochLedger Read(ReadOnlySpan<byte> bytes)
    {
        if (bytes.IsEmpty) return ContractEpochLedger.Empty;
        string text;
        try
        {
            text = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("contract epoch ledger must be strict UTF-8", exception);
        }

        if (!text.EndsWith('\n') || text.Contains('\r'))
        {
            throw new FormatException("contract epoch ledger must use LF and end with one LF");
        }

        var lines = text.Split('\n');
        if (lines[..^1].Any(static line => line.Length == 0))
        {
            throw new FormatException("contract epoch ledger must not contain blank lines");
        }

        var events = ImmutableArray.CreateBuilder<ContractEpochEvent>();
        foreach (var line in lines[..^1])
        {
            var raw = StrictUtf8.GetBytes(line + "\n");
            ImmutableArray<byte> canonical;
            try
            {
                canonical = StructuredCanonicalWriter.WriteJson(line);
            }
            catch (JsonException exception)
            {
                throw new FormatException("contract epoch ledger line is not valid JSON", exception);
            }

            if (!canonical.AsSpan().SequenceEqual(raw))
            {
                throw new FormatException("contract epoch ledger line is not canonical JSON");
            }

            try
            {
                using var document = JsonDocument.Parse(line);
                events.Add(ReadEvent(document.RootElement));
            }
            catch (ArgumentException exception)
            {
                throw new FormatException(exception.Message, exception);
            }
        }

        ValidateLifecycle(events);
        return ContractEpochLedger.Create(events.ToImmutable(), ImmutableArray.CreateRange(bytes.ToArray()));
    }

    private static JsonElement EventElement(ContractEpochEvent item) => item switch
    {
        ContractEpochEvent.Register registration => JsonSerializer.SerializeToElement(new
        {
            baseline_tree_oid = registration.BaselineTreeOid,
            event_type = "register",
            plan = TransitionPlanCodec.Element(registration.Plan),
            plan_id = registration.PlanId,
            plan_root = registration.PlanRoot,
            post_policy_root = registration.PostPolicyRoot,
            pre_policy_root = registration.PrePolicyRoot,
        }),
        ContractEpochEvent.Consume consumption => JsonSerializer.SerializeToElement(new
        {
            event_type = "consume",
            plan_id = consumption.PlanId,
        }),
        _ => throw new InvalidOperationException("unknown contract epoch event"),
    };

    private static ContractEpochEvent ReadEvent(JsonElement root)
    {
        var eventType = RequiredString(root, "event_type");
        if (string.Equals(eventType, "consume", StringComparison.Ordinal))
        {
            RequireProperties(root, "event_type", "plan_id");
            return new ContractEpochEvent.Consume(RequiredString(root, "plan_id"));
        }

        if (!string.Equals(eventType, "register", StringComparison.Ordinal))
        {
            throw new FormatException($"unknown contract epoch event type: {eventType}");
        }

        RequireProperties(
            root,
            "baseline_tree_oid",
            "event_type",
            "plan",
            "plan_id",
            "plan_root",
            "post_policy_root",
            "pre_policy_root");
        var registration = new ContractEpochEvent.Register(
            RequiredString(root, "plan_id"),
            RequiredString(root, "baseline_tree_oid"),
            RequiredString(root, "pre_policy_root"),
            RequiredString(root, "post_policy_root"),
            TransitionPlanCodec.ReadElement(root.GetProperty("plan")));
        if (!string.Equals(
            registration.PlanRoot,
            RequiredString(root, "plan_root"),
            StringComparison.Ordinal))
        {
            throw new FormatException("contract epoch plan root does not match its canonical plan");
        }

        return registration;
    }

    private static void ValidateLifecycle(IEnumerable<ContractEpochEvent> events)
    {
        var registered = new HashSet<string>(StringComparer.Ordinal);
        var consumed = new HashSet<string>(StringComparer.Ordinal);
        foreach (var item in events)
        {
            switch (item)
            {
                case ContractEpochEvent.Register registration when !registered.Add(registration.PlanId):
                    throw new FormatException($"contract epoch plan is registered more than once: {registration.PlanId}");
                case ContractEpochEvent.Consume consumption when !registered.Contains(consumption.PlanId):
                    throw new FormatException($"contract epoch plan was consumed before registration: {consumption.PlanId}");
                case ContractEpochEvent.Consume consumption when !consumed.Add(consumption.PlanId):
                    throw new FormatException($"contract epoch plan was consumed more than once: {consumption.PlanId}");
            }
        }
    }

    private static void RequireProperties(JsonElement element, params string[] expected)
    {
        if (element.ValueKind is not JsonValueKind.Object
            || !element.EnumerateObject().Select(static item => item.Name)
                .SequenceEqual(expected, StringComparer.Ordinal))
        {
            throw new FormatException("contract epoch event keys are not canonical");
        }
    }

    private static string RequiredString(JsonElement root, string property)
    {
        var value = root.GetProperty(property);
        return value.ValueKind is JsonValueKind.String && value.GetString() is { Length: > 0 } text
            ? text
            : throw new FormatException($"contract epoch {property} must be a non-empty string");
    }
}
