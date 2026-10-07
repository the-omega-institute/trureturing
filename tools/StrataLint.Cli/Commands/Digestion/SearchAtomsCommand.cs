using System.Globalization;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class SearchAtomsCommand
{
    internal static CommandResult Run(IRepositoryGateway repository, IReadOnlyList<string> arguments)
    {
        try
        {
            var options = Parse(arguments);
            var sourceIds = options.Sources.Any(static source => source.Contains('/'))
                ? DigestionQuerySelection.ResolveSources(repository, options.Sources)
                : options.Sources;
            foreach (var source in sourceIds)
                if (!RepoPath.TryCreate(source, out _) || source.Contains('/')) throw Usage();
            var paths = repository.SearchCurrentPaths(sourceIds.Select(source =>
                DigestionQuerySelection.Literal(BackfillInventoryLoader.RootPath + source)).ToArray());
            var output = new StringBuilder();
            foreach (var path in paths.Where(DigestionQuerySelection.IsAtomPath).Order(StringComparer.Ordinal)
                         .Where(BackfillInventoryLoader.IsCanonicalPath)
                         .Where(path => options.States.Contains(State(path), StringComparer.Ordinal))
                         .Where(path => DigestionNonpropositional.IsAtomId(Path.GetFileNameWithoutExtension(path)))
                         .Where(path => options.Text is null || CasContains(repository, Path.GetFileNameWithoutExtension(path), options.Text))
                         .Take(options.Limit))
                output.AppendLine($"ATOM source_id={DigestionQuerySelection.SourceId(path)} atom_id={Path.GetFileNameWithoutExtension(path)} state={State(path)} path={path}");
            return new(true, output.ToString(), string.Empty);
        }
        catch (Exception error) when (error is FormatException or InvalidOperationException or IOException or ArgumentException)
        {
            return new(false, string.Empty, $"SEARCH_ATOMS_INVALID {error.Message}\n");
        }
    }

    private static bool CasContains(IRepositoryGateway repository, string id, string text)
    {
        var path = DigestionCasStore.RootPath + id;
        var raw = repository.ReadCurrent([DigestionQuerySelection.Literal(path)]);
        var blob = raw.Entries.SingleOrDefault(entry => entry.Path == path);
        return blob is not null && Encoding.UTF8.GetString(blob.Bytes.AsSpan())
            .Contains(text, StringComparison.OrdinalIgnoreCase);
    }

    private static string State(string path) => path.Split('/')[^2];

    private static Options Parse(IReadOnlyList<string> arguments)
    {
        var sources = new List<string>();
        var states = new List<string>();
        string? text = null;
        var limit = 100;
        var hasLimit = false;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count || string.IsNullOrWhiteSpace(arguments[index + 1])) throw Usage();
            var value = arguments[index + 1];
            switch (arguments[index])
            {
                case "--source": sources.Add(value); break;
                case "--state" when !value.Contains('/') && !value.Any(char.IsWhiteSpace): states.Add(value); break;
                case "--text" when text is null: text = value; break;
                case "--limit" when !hasLimit && int.TryParse(value, NumberStyles.None, CultureInfo.InvariantCulture, out limit) && limit > 0:
                    hasLimit = true; break;
                default: throw Usage();
            }
        }
        if (sources.Count == 0) throw Usage();
        return new(sources.Distinct(StringComparer.Ordinal).ToArray(),
            states.Count == 0 ? ["residual-open", "residual-closed", "residual-tail", "partial-open", "partial-closed", "partial-tail"]
                : states.ToArray(), text, limit);
    }

    private static FormatException Usage() => new(
        "USAGE: StrataLint search-atoms --source SOURCE_ID_OR_PATH [--source ...] [--text LITERAL] [--state STATE ...] [--limit N]");

    private sealed record Options(string[] Sources, string[] States, string? Text, int Limit);
}
