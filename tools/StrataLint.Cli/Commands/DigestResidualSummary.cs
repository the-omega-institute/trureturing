using System.Collections.Immutable;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

// 由 DigestStatusCommand.cs 拆出(2026-08-30,#4125):该文件加入 quarantine 投影后 832 行,越过 SL-003 的 800 硬线。
// 同目录下的 .cs 仍在 DigestionEvaluationScopes.ForChanges 的 caller-implementation 匹配范围内
// (IsCallerImplementationPath 按目录匹配),故拆分不改变全量重算的触发面。
internal static class DigestResidualSummary
{
    private const string ResidualGapCode = "unresolved-subitem";
    private const string ShardDirectory = "Generated/echo-residuals/";

    internal static IReadOnlyDictionary<string, string> RenderShards(
        DigestionLedgerEvaluation evaluation,
        DigestionFrontierProjection frontier)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        ArgumentNullException.ThrowIfNull(frontier);
        var excludedAtomIds = ExcludedAtomIds(frontier);
        var shards = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var source in evaluation.Entries
                     .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                     .OrderBy(static group => group.Key, StringComparer.Ordinal))
        {
            var atoms = source
                .Where(item => !excludedAtomIds.Contains(item.Entry.AtomId))
                .Select(static item => new AtomResiduals(
                    item.Entry.AtomId,
                    item.Gaps
                        .Where(static gap => gap.Code == ResidualGapCode)
                        .Select(static gap => gap.Detail)
                        .OrderBy(static detail => detail, StringComparer.Ordinal)
                        .ToArray()))
                .Where(static atom => atom.Subitems.Length > 0)
                .OrderBy(static atom => atom.AtomId, StringComparer.Ordinal)
                .ToArray();
            var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
            writer.WriteLine($"# Echo Residual Summary — `{source.Key}`");
            writer.WriteLine();
            writer.WriteLine($"- unresolved_subitems: {atoms.Sum(static atom => atom.Subitems.Length)}");
            writer.WriteLine($"- mother_residual_atom_ids: {atoms.Length}");
            writer.WriteLine();
            if (atoms.Length == 0)
            {
                writer.WriteLine("Mother residual atoms: none.");
            }
            else
            {
                writer.WriteLine("Mother residual atoms:");
                writer.WriteLine();
                foreach (var atom in atoms)
                {
                    writer.WriteLine($"- `{atom.AtomId}` ({atom.Subitems.Length})");
                    foreach (var subitem in atom.Subitems)
                    {
                        writer.WriteLine($"  - `{subitem}`");
                    }
                }
            }

            shards.Add(
                $"{ShardDirectory}{source.Key}.md",
                EchoResidualBlock.RenderShard(source.Key, writer.ToString()));
        }

        return shards;
    }

    internal static string Render(
        DigestionLedgerEvaluation evaluation,
        DigestionFrontierProjection frontier)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        ArgumentNullException.ThrowIfNull(frontier);
        var excludedAtomIds = ExcludedAtomIds(frontier);
        var sources = evaluation.Entries
            .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
            .OrderBy(static group => group.Key, StringComparer.Ordinal)
            .Select(group => new SourceResiduals(
                group.Key,
                group
                    .Where(item => !excludedAtomIds.Contains(item.Entry.AtomId))
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
        var sharedResidues = sources
            .SelectMany(static source => source.Atoms.SelectMany(atom =>
                atom.Subitems.Select(residue => new ResidueHost(residue, source.SourceId, atom.AtomId))))
            .GroupBy(static host => host.Residue, StringComparer.Ordinal)
            .Select(static group => new SharedResidue(
                group.Key,
                group.Distinct().OrderBy(static host => host.SourceId, StringComparer.Ordinal)
                    .ThenBy(static host => host.AtomId, StringComparer.Ordinal)
                    .ToArray()))
            .Where(static residue => residue.Hosts
                .Select(static host => host.SourceId)
                .Distinct(StringComparer.Ordinal)
                .Count() > 1)
            .OrderBy(static residue => residue.Name, StringComparer.Ordinal)
            .ToArray();
        var quarantined = frontier.Entries
            .Where(static item =>
                item.PrimaryDisposition == DigestionFrontierDisposition.Quarantined)
            .Select(static item => new QuarantinedResiduals(
                item.Entry.SourceId,
                item.Entry.AtomId,
                item.Entry.Receipts.Quarantine!,
                item.Evaluation.Gaps
                    .Where(static gap => gap.Code == ResidualGapCode)
                    .Select(static gap => gap.Detail)
                    .OrderBy(static detail => detail, StringComparer.Ordinal)
                    .ToArray()))
            .Where(static item => item.Subitems.Length > 0)
            .OrderBy(static item => item.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.AtomId, StringComparer.Ordinal)
            .ToArray();
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine("# Echo Residual Summary");
        writer.WriteLine();
        writer.WriteLine($"- unresolved_subitems: {sources.Sum(static source => source.SubitemCount)}");
        writer.WriteLine($"- mother_residual_atom_ids: {sources.Sum(static source => source.Atoms.Length)}");
        writer.WriteLine();
        RenderFrontier(writer, frontier);
        writer.WriteLine();
        writer.WriteLine("## quarantined residuals");
        writer.WriteLine();
        writer.WriteLine($"- quarantined_subitems: {quarantined.Sum(static item => item.Subitems.Length)}");
        writer.WriteLine($"- mother_quarantined_atom_ids: {quarantined.Length}");
        writer.WriteLine();
        if (quarantined.Length == 0)
        {
            writer.WriteLine("Quarantined residual atoms: none.");
        }
        else
        {
            writer.WriteLine("Quarantined residual atoms:");
            writer.WriteLine();
            foreach (var item in quarantined)
            {
                writer.WriteLine($"- `{item.SourceId}/{item.AtomId}` ({item.Subitems.Length})");
                writer.WriteLine($"  - justification: `{item.Quarantine.Justification}`");
                writer.WriteLine($"  - reentry_condition: `{item.Quarantine.ReentryCondition}`");
                foreach (var subitem in item.Subitems)
                {
                    writer.WriteLine($"  - `{subitem}`");
                }
            }
        }

        writer.WriteLine();
        writer.WriteLine("## cross-volume shared residues");
        writer.WriteLine();
        writer.WriteLine($"- shared_residue_names: {sharedResidues.Length}");
        writer.WriteLine($"- host_atoms: {sharedResidues.Sum(static residue => residue.Hosts.Length)}");
        writer.WriteLine();
        if (sharedResidues.Length == 0)
        {
            writer.WriteLine("Shared residue hosts: none.");
        }
        else
        {
            writer.WriteLine("Shared residue hosts:");
            writer.WriteLine();
            foreach (var residue in sharedResidues)
            {
                var volumeCount = residue.Hosts
                    .Select(static host => host.SourceId)
                    .Distinct(StringComparer.Ordinal)
                    .Count();
                var hosts = string.Join(
                    ", ",
                    residue.Hosts.Select(static host => $"`{host.SourceId}/{host.AtomId}`"));
                writer.WriteLine(
                    $"- `{residue.Name}` ({volumeCount} volumes, {residue.Hosts.Length} host atoms): {hosts}");
            }
        }

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

    private static ImmutableHashSet<string> ExcludedAtomIds(
        DigestionFrontierProjection frontier) => frontier.Entries
        .Where(static entry => entry.PrimaryDisposition is
            DigestionFrontierDisposition.Quarantined or DigestionFrontierDisposition.Withheld)
        .Select(static entry => entry.Entry.AtomId)
        .ToImmutableHashSet(StringComparer.Ordinal);

    private static void RenderFrontier(
        StringWriter writer,
        DigestionFrontierProjection frontier)
    {
        writer.WriteLine("## frontier");
        writer.WriteLine();
        RenderFrontierCounts(writer, frontier.Total);
        writer.WriteLine();
        writer.WriteLine("Per-source frontier:");
        writer.WriteLine();
        foreach (var source in frontier.PerSource)
        {
            writer.WriteLine($"- `{source.SourceId}`");
            RenderFrontierCounts(writer, source.Counts, "  ");
        }
    }

    private static void RenderFrontierCounts(
        StringWriter writer,
        DigestionFrontierCounts counts,
        string indent = "")
    {
        writer.WriteLine($"{indent}- residual_open: {counts.ResidualOpen}");
        writer.WriteLine($"{indent}- formalization_frontier: {counts.FormalizationFrontier}");
        writer.WriteLine($"{indent}- quarantined: {counts.Quarantined}");
        writer.WriteLine($"{indent}- withheld: {counts.Withheld}");
        writer.WriteLine($"{indent}- chain_child: {counts.ChainChild}");
        writer.WriteLine($"{indent}- not_formalizable: {counts.NotFormalizable}");
        writer.WriteLine($"{indent}- formalizable_claim: {counts.FormalizableClaim}");
    }

    private sealed record AtomResiduals(string AtomId, string[] Subitems);

    private sealed record ResidueHost(string Residue, string SourceId, string AtomId);

    private sealed record SharedResidue(string Name, ResidueHost[] Hosts);

    private sealed record QuarantinedResiduals(
        string SourceId,
        string AtomId,
        DigestionQuarantine Quarantine,
        string[] Subitems);

    private sealed record SourceResiduals(string SourceId, AtomResiduals[] Atoms)
    {
        internal int SubitemCount => Atoms.Sum(static atom => atom.Subitems.Length);
    }
}
