using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private static InvalidOperationException SourceUsage(string reason) => new(
        "USAGE: StrataLint ingest --base REV [--source X]...; " + reason);

    private static (ImmutableHashSet<string>? SourceIds, ImmutableHashSet<string>? RegistrationPaths) ResolveSources(
        IngestInputs inputs,
        ImmutableArray<string> selectors)
    {
        if (selectors.IsEmpty) return (null, null);

        var sources = inputs.CurrentDocument.RequireDigestionSources();
        var claims = sources.ToDictionary(static source => source.SourceId,
            static source => source.SourcePath, StringComparer.Ordinal);
        var ids = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var paths = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var selector in selectors)
        {
            var registered = sources.FirstOrDefault(source => source.SourceId == selector || source.SourcePath == selector);
            if (registered is not null)
            {
                ids.Add(registered.SourceId);
                continue;
            }
            if (!selector.StartsWith(DigestionOpaquePathPolicy.TheoryRootPath, StringComparison.Ordinal)
                || !selector.EndsWith(".md", StringComparison.Ordinal)
                || !inputs.Current.TryGetFile(selector, out _))
                throw SourceUsage($"unknown --source selector '{selector}'");

            var id = DigestionIngestor.DeriveSourceId(selector);
            if (claims.TryGetValue(id, out var claimant) && claimant != selector)
                throw SourceUsage($"--source selector '{selector}' collides with '{claimant}': {id}");
            claims[id] = selector;
            ids.Add(id);
            paths.Add(selector);
        }
        return (ids.ToImmutable(), paths.ToImmutable());
    }

}
