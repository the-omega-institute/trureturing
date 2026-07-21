using System.Collections.Immutable;

namespace StrataLint.Engine;

internal delegate AtomizedTheoryDocument TheoryAtomizer(ReadOnlySpan<byte> bytes);

internal sealed record AtomizerRegistration(
    TheoryAtomizer Atomize,
    string ResidualPrefix);

internal static class AtomizerRegistry
{
    internal const string GictId = "gict-v1";
    internal const string ObserverId = "observer-v1";
    internal const string PeriodicTreeId = "periodic-tree-v1";
    internal const string PzgId = "pzg-v1";
    internal const string NoAtomizerId = "none";

    private static readonly ImmutableDictionary<string, AtomizerRegistration> Atomizers =
        ImmutableDictionary<string, AtomizerRegistration>.Empty
            .WithComparers(StringComparer.Ordinal)
            .Add(GictId, new AtomizerRegistration(GictAtomizer.Atomize, "gict"))
            .Add(ObserverId, new AtomizerRegistration(ObserverAtomizer.Atomize, "observer"))
            .Add(
                PeriodicTreeId,
                new AtomizerRegistration(PeriodicTreeAtomizer.Atomize, "periodic-tree"))
            .Add(PzgId, new AtomizerRegistration(PzgAtomizer.Atomize, "pzg"));

    internal static ImmutableArray<string> RegisteredIds { get; } =
        Atomizers.Keys.Order(StringComparer.Ordinal).ToImmutableArray();

    internal static AtomizedTheoryDocument Atomize(
        string id,
        ReadOnlySpan<byte> bytes)
    {
        if (id == NoAtomizerId)
        {
            throw new FormatException(
                "Source has no deterministic atomizer. Registered atomizers: "
                + string.Join(", ", RegisteredIds)
                + ".");
        }

        return Require(id).Atomize(bytes);
    }

    internal static bool IsRegistered(string id) => Atomizers.ContainsKey(id);

    internal static AtomizerRegistration Require(string id) =>
        Atomizers.TryGetValue(id, out var registration)
            ? registration
            : throw Unknown(id);

    private static FormatException Unknown(string id) => new(
        $"Unknown atomizer id '{id}'. Registered atomizers: "
        + string.Join(", ", RegisteredIds)
        + ".");
}
