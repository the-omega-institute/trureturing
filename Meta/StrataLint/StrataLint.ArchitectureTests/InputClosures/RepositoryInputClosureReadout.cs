using System.Text;

namespace StrataLint.ArchitectureTests;

internal static class RepositoryInputClosureReadout
{
    internal static string Render(RepositoryInputClosureResult result)
    {
        var builder = new StringBuilder("project\tsource\ttest\teffects\treason\n");
        foreach (var effect in result.OrderBy(static effect => effect.Project, StringComparer.Ordinal)
                     .ThenBy(static effect => effect.SourcePath, StringComparer.Ordinal)
                     .ThenBy(static effect => effect.Method, StringComparer.Ordinal))
        {
            builder.Append(effect.Project).Append('\t')
                .Append(effect.SourcePath).Append('\t')
                .Append(effect.Method).Append('\t')
                .AppendJoin(',', effect.Patterns).Append('\t');
            if (effect.Patterns.Contains("All", StringComparer.Ordinal))
            {
                builder.Append("fail-closed: no narrower repository-read effect was proven");
            }
            builder.Append('\n');
        }

        foreach (var finding in result.DeclarationFindings.Order(StringComparer.Ordinal))
        {
            builder.Append("VIOLATION\t").Append(finding).Append('\n');
        }
        return builder.ToString();
    }
}
