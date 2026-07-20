using System.Globalization;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestResidualSummary
{
    private const string ResidualGapCode = "unresolved-subitem";

    internal static string Render(DigestionLedgerEvaluation evaluation)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        var sources = evaluation.Entries
            .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
            .OrderBy(static group => group.Key, StringComparer.Ordinal)
            .Select(static group => new SourceResiduals(
                group.Key,
                group
                    .Select(static item => new AtomResiduals(
                        item.Entry.AtomId,
                        item.Gaps
                            .Where(static gap => gap.Code == ResidualGapCode)
                            .Select(static gap => gap.Detail)
                            .OrderBy(static detail => detail, StringComparer.Ordinal)
                            .ToArray()))
                    .Where(static item => item.Subitems.Length > 0)
                    .OrderBy(static item => item.AtomId, StringComparer.Ordinal)
                    .ToArray()))
            .ToArray();
        var writer = new StringWriter(CultureInfo.InvariantCulture);
        writer.WriteLine("# Echo Residual Summary");
        writer.WriteLine();
        writer.WriteLine($"- unresolved_subitems: {sources.Sum(static source => source.SubitemCount)}");
        writer.WriteLine($"- mother_residual_atom_ids: {sources.Sum(static source => source.Atoms.Length)}");

        foreach (var source in sources)
        {
            writer.WriteLine();
            writer.WriteLine($"## `{source.SourceId}`");
            writer.WriteLine();
            writer.WriteLine($"- unresolved_subitems: {source.SubitemCount}");
            writer.WriteLine($"- mother_residual_atom_ids: {source.Atoms.Length}");
            writer.WriteLine();
            if (source.Atoms.Length == 0)
            {
                writer.WriteLine("Mother residual atoms: none.");
                continue;
            }

            writer.WriteLine("Mother residual atoms:");
            writer.WriteLine();
            foreach (var atom in source.Atoms)
            {
                writer.WriteLine($"- `{atom.AtomId}` ({atom.Subitems.Length})");
                foreach (var subitem in atom.Subitems)
                {
                    writer.WriteLine($"  - `{subitem}`");
                }
            }
        }

        return writer.ToString();
    }

    private sealed record AtomResiduals(string AtomId, string[] Subitems);

    private sealed record SourceResiduals(string SourceId, AtomResiduals[] Atoms)
    {
        internal int SubitemCount => Atoms.Sum(static atom => atom.Subitems.Length);
    }
}
