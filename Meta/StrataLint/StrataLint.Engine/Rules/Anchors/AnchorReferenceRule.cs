using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class AnchorReferenceRule
{
    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
        var catalog = AnchorCatalogLoader.Load(context.Current);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, file) in RepositoryRules.FormalFiles(context.Current)
            .OrderBy(static item => item.Path.Value, StringComparer.Ordinal))
        {
            if (!RepositoryRules.TryHeader(file.Text, out var header))
            {
                continue;
            }

            foreach (var anchor in header.Anchors)
            {
                if (!catalog.Definitions.ContainsKey(anchor))
                {
                    findings.Add(new RuleFinding(
                        path.Value,
                        $"anchor '{anchor}' is unregistered (Unregistered) in the typed catalog"));
                }
            }
        }

        return findings.ToImmutable();
    }
}
