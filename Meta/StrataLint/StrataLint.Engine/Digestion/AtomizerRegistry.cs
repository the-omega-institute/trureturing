using System.Collections.Immutable;

namespace StrataLint.Engine;

internal delegate AtomizedTheoryDocument TheoryAtomizer(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules);

internal sealed record AtomizerRegistration(
    TheoryAtomizer Atomize,
    string ResidualPrefix);

internal static class AtomizerRegistry
{
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
            .Add(ConeId, new AtomizerRegistration(ConeAtomizer.Atomize, "cone"))
            .Add(GictId, new AtomizerRegistration(GictAtomizer.Atomize, "gict"))
            .Add(ObserverId, new AtomizerRegistration(ObserverAtomizer.Atomize, "observer"))
            .Add(
                PeriodicTreeId,
                new AtomizerRegistration(PeriodicTreeAtomizer.Atomize, "periodic-tree"))
            .Add(PzgId, new AtomizerRegistration(PzgAtomizer.Atomize, "pzg"))
            .Add(WmId, new AtomizerRegistration(WmAtomizer.Atomize, "wm"));

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

    internal static AtomizerRegistration Require(string id) =>
        Atomizers.TryGetValue(id, out var registration)
            ? registration
            : IsDeclaredDialect(id)
                // A declared dialect resolves its rules at atomization, not here: the
                // registration only needs the residual stem, which the id already carries.
                ? new AtomizerRegistration(
                    (bytes, rules) => DeclaredDialectAtomizer.Atomize(id, bytes, rules),
                    id[DeclaredDialectAtomizer.IdPrefix.Length..])
                : throw Unknown(id);

    private static FormatException Unknown(string id) => new(
        $"Unknown atomizer id '{id}'. Registered atomizers: "
        + string.Join(", ", RegisteredIds)
        + ".");
}
