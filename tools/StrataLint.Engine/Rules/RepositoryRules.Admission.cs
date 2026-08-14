using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> Axioms(RuleEvaluationContext context)
    {
        const string debtPath = "D5/X_Assumptions/AxiomDebt.lean";
        var registered = ImmutableHashSet<string>.Empty;
        if (RepoPath.TryCreate(debtPath, out var debtRepoPath)
            && context.Lean.Report.Files.TryGetValue(debtRepoPath, out var debt))
        {
            registered = debt.Declarations
                .Where(static declaration => declaration.Kind == "axiom")
                .Select(static declaration => declaration.Name)
                .ToImmutableHashSet(StringComparer.Ordinal);
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files)
        {
            if (!string.IsNullOrEmpty(report.Error))
            {
                findings.Add(new RuleFinding(path.Value, $"Lean environment inspection failed: {report.Error}"));
                continue;
            }

            var direct = report.Declarations
                .Where(static declaration => declaration.Kind == "axiom")
                .Select(static declaration => declaration.Name)
                .ToImmutableHashSet(StringComparer.Ordinal);
            if (path.Value != debtPath && direct.Count > 0)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "axiom declarations are confined to AxiomDebt.lean: "
                    + string.Join(", ", direct.Order(StringComparer.Ordinal))));
            }

            var extra = report.Declarations
                .SelectMany(static declaration => declaration.Axioms)
                .Where(axiom => axiom != "sorryAx"
                    && !direct.Contains(axiom)
                    && !registered.Contains(axiom)
                    && !LeanAxiomFacts.IsStandard(axiom))
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (extra.Length > 0)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "unregistered transitive axiom closure: " + string.Join(", ", extra)));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Instantiation(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var path in context.Current.Files.Keys)
        {
            var parts = path.Value.Split('/');
            var theory = parts.Length > 1 && (parts[0] is "Blueprint" or "Evidence")
                ? parts[1]
                : parts[0];
            if (theory is "Metallic" or "Moduli"
                || theory.Length > 1 && theory[0] == 'D' && theory != "D5" && theory[1..].All(char.IsDigit))
            {
                findings.Add(new RuleFinding(path.Value, $"{theory} 未实例化(压力未至,D5-T0009)"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Bootstrap(RuleEvaluationContext context) =>
        context.Changes.Paths
            .Where(BootstrapGate.IsProtected)
            .Select(static path => new RuleFinding(path.Value, BootstrapGate.ProtectedSurfaceMessage))
            .ToImmutableArray();
}
