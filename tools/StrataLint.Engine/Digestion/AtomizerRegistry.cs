using System.Collections.Immutable;

namespace StrataLint.Engine;

internal delegate AtomizedTheoryDocument TheoryAtomizer(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules);

internal sealed record AtomizerRegistration(
    TheoryAtomizer Atomize,
    bool EmitsClausePlans = false);

internal static class AtomizerRegistry
{
    /// <summary>
    /// The atomizer a source gets when no dialect has been written for it. It is a rule
    /// rather than a lexicon, so it needs no registration data and never rejects a shape.
    /// </summary>
    internal const string GenericId = "generic-v1";
    internal const string ConeId = "cone-v1";
    internal const string GictId = "gict-v1";
    internal const string ObserverId = "observer-v1";
    internal const string PeriodicTreeId = "periodic-tree-v1";
    internal const string PzgId = "pzg-v1";
    internal const string WmId = "wm-v1";
    internal const string NoAtomizerId = "none";

    private static readonly ImmutableDictionary<string, AtomizerRegistration> Atomizers =
        ImmutableDictionary<string, AtomizerRegistration>.Empty
            .WithComparers(StringComparer.Ordinal)
            .Add(
                GenericId,
                new AtomizerRegistration(GenericAtomizer.Atomize))
            .Add(ConeId, new AtomizerRegistration(ConeAtomizer.Atomize))
            .Add(GictId, new AtomizerRegistration(GictAtomizer.Atomize))
            .Add(ObserverId, new AtomizerRegistration(ObserverAtomizer.Atomize))
            .Add(
                PeriodicTreeId,
                new AtomizerRegistration(PeriodicTreeAtomizer.Atomize))
            .Add(PzgId, new AtomizerRegistration(PzgAtomizer.Atomize, EmitsClausePlans: true))
            .Add(WmId, new AtomizerRegistration(WmAtomizer.Atomize));

    internal static ImmutableArray<string> RegisteredIds { get; } =
        Atomizers.Keys.Order(StringComparer.Ordinal).ToImmutableArray();

    internal static AtomizedTheoryDocument Atomize(
        string id,
        ReadOnlySpan<byte> bytes,
        TheoryAtomizerRules rules)
    {
        if (id == NoAtomizerId)
        {
            throw new FormatException(
                "Source has no deterministic atomizer. Registered atomizers: "
                + string.Join(", ", RegisteredIds)
                + ".");
        }

        return Require(id).Atomize(bytes, rules);
    }

    /// <summary>
    /// A dialect declared in atomizer data rather than registered in code. Its identity is
    /// resolved against the loaded rules at use, so a new volume needs data, not a build.
    /// </summary>
    internal static bool IsDeclaredDialect(string id) =>
        id.StartsWith(DeclaredDialectAtomizer.IdPrefix, StringComparison.Ordinal);

    internal static bool IsRegistered(string id) =>
        Atomizers.ContainsKey(id) || IsDeclaredDialect(id);

    internal static bool EmitsClausePlans(string id) => Require(id).EmitsClausePlans;

    internal static AtomizerRegistration Require(string id) =>
        Atomizers.TryGetValue(id, out var registration)
            ? registration
            : IsDeclaredDialect(id)
                ? new AtomizerRegistration(
                    (bytes, rules) => DeclaredDialectAtomizer.Atomize(id, bytes, rules))
                : throw Unknown(id);

    private static FormatException Unknown(string id) => new(
        $"Unknown atomizer id '{id}'. Registered atomizers: "
        + string.Join(", ", RegisteredIds)
        + ".");
}
