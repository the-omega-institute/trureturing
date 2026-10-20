using System.Collections.Immutable;

namespace StrataLint.Engine;

internal delegate AtomizedTheoryDocument TheoryAtomizer(ReadOnlySpan<byte> bytes);

internal delegate AtomizedTheoryDocument TheoryAtomizerWithContentKinds(
    ReadOnlySpan<byte> bytes,
    IDictionary<string, string>? contentKinds);

internal sealed record AtomizerRegistration(
    TheoryAtomizer Atomize,
    TheoryAtomizerWithContentKinds AtomizeWithContentKinds);

internal static class AtomizerRegistry
{
    internal const string GenericId = "generic-v1";

    private static readonly ImmutableDictionary<string, AtomizerRegistration> Atomizers =
        ImmutableDictionary<string, AtomizerRegistration>.Empty
            .WithComparers(StringComparer.Ordinal)
            .Add(GenericId, new AtomizerRegistration(
                GenericAtomizer.Atomize, GenericAtomizer.AtomizeWithContentKinds));

    internal static ImmutableArray<string> RegisteredIds { get; } =
        Atomizers.Keys.Order(StringComparer.Ordinal).ToImmutableArray();

    internal static AtomizedTheoryDocument Atomize(
        string id,
        ReadOnlySpan<byte> bytes)
    {
        return Require(id).Atomize(bytes);
    }

    internal static ImmutableDictionary<string, string> ResolveContentKinds(
        string id,
        ReadOnlySpan<byte> bytes)
    {
        var kinds = new Dictionary<string, string>(StringComparer.Ordinal);
        var document = Require(id).AtomizeWithContentKinds(bytes, kinds);
        if (document.ClausePlans.IsEmpty)
            InheritClauseContentKinds(kinds, document.Claims.Select(DigestionDecomposition.PlanClauses)
                .OfType<DigestionClausePlan>());
        return kinds.ToImmutableDictionary(StringComparer.Ordinal);
    }

    internal static bool IsRegistered(string id) => id == GenericId;

    internal static AtomizerRegistration Require(string id) =>
        Atomizers.TryGetValue(id, out var registration) ? registration : throw Unknown(id);

    internal static ImmutableDictionary<string, string> CaptureContentKinds(
        Action<IDictionary<string, string>> atomize)
    {
        ArgumentNullException.ThrowIfNull(atomize);
        var kinds = new Dictionary<string, string>(StringComparer.Ordinal);
        atomize(kinds);
        return kinds.ToImmutableDictionary(StringComparer.Ordinal);
    }

    internal static void RecordContentKind(
        IDictionary<string, string>? kinds,
        DigestionAtom atom,
        string kind)
    {
        if (kinds is null || string.IsNullOrEmpty(kind))
        {
            return;
        }

        var hash = atom.Fingerprints.RawSha256;
        if (kinds.TryGetValue(hash, out var existing) && existing != kind)
        {
            kinds.Remove(hash);
            return;
        }

        kinds[hash] = kind;
    }

    internal static void InheritClauseContentKinds(
        IDictionary<string, string>? kinds,
        IEnumerable<DigestionClausePlan> plans)
    {
        if (kinds is null)
        {
            return;
        }

        var pending = new Queue<DigestionClausePlan>(plans);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (pending.TryDequeue(out var plan))
        {
            if (!visited.Add(plan.Parent.Fingerprints.RawSha256)
                || !kinds.TryGetValue(plan.Parent.Fingerprints.RawSha256, out var kind))
            {
                continue;
            }

            foreach (var child in plan.Children)
            {
                RecordContentKind(kinds, child, kind);
                if (DigestionDecomposition.PlanClauses(child) is { } nested)
                    pending.Enqueue(nested);
            }
        }
    }

    private static FormatException Unknown(string id) => new(
        $"Unknown atomizer id '{id}'. Registered atomizers: "
        + string.Join(", ", RegisteredIds)
        + ".");
}
