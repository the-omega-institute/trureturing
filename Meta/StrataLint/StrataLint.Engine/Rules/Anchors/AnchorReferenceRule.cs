using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class AnchorReferenceRule
{
    internal static ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context)
    {
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
                // Anchor syntax is another rule's finding; an unparsable value is not this rule's business.
                if (Anchor.TryParseCanonical(anchor) is not AnchorParseResult.Parsed parsed)
                {
                    continue;
                }

                // The Lean import graph is the only authority this rule can check an anchor against,
                // and it only carries module edges. An anchor shape it cannot decide stays rejected —
                // that is exactly what the retired registry did to every unregistered anchor.
                if (parsed.Value is not MathlibAnchor { TargetKind: MathlibTargetKind.Module } module)
                {
                    findings.Add(new RuleFinding(
                        path.Value,
                        $"anchor '{anchor}' cannot be decided against the Lean import graph; "
                        + "only mathlib/module anchors are verifiable there"));
                    continue;
                }

                if (!LeanImportClosure.ImportsExternalModule(
                    context.Lean.Report,
                    LeanImportClosure.ModuleName(path),
                    module.Name.Value))
                {
                    findings.Add(new RuleFinding(
                        path.Value,
                        $"anchor '{anchor}' is not reachable through this file's repository import closure"));
                }
            }
        }

        return findings.ToImmutable();
    }
}
