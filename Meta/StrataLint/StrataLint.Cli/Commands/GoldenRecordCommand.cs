using System.Globalization;
using StrataLint.Definitions;

namespace StrataLint.Cli;

internal static class GoldenRecordCommand
{
    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 0)
            {
                return Invalid("USAGE: StrataLint golden-record");
            }

            var root = Path.GetFullPath(repositoryRoot);
            var corpus = TomlGoldenLoader.LoadRepository(root);
            var outputs = new List<(string Path, byte[] Bytes, bool Changed)>(corpus.Files.Count);
            foreach (var file in corpus.Files)
            {
                var recorded = file.Cases.Select(testCase => testCase with
                {
                    ExpectedDiagnostics = GoldenCorpusMaterializer.Evaluate(root, testCase)
                        .OrderBy(static item => item.RuleId.Value, StringComparer.Ordinal)
                        .ThenBy(static item => item.Path, StringComparer.Ordinal)
                        .ThenBy(static item => item.Message, StringComparer.Ordinal)
                        .Select(static item => new GoldenDiagnostic(
                            RuleNumber(item.RuleId.Value),
                            item.Path,
                            item.Message))
                        .ToArray(),
                }).ToArray();
                var bytes = TomlGoldenWriter.Write(recorded);
                outputs.Add((
                    file.Path,
                    bytes,
                    !bytes.AsSpan().SequenceEqual(File.ReadAllBytes(file.Path))));
            }

            foreach (var output in outputs.Where(static item => item.Changed))
            {
                File.WriteAllBytes(output.Path, output.Bytes);
            }

            return new CommandResult(
                true,
                $"GOLDEN_RECORDED cases={corpus.Cases.Count} "
                + $"changed_files={outputs.Count(static item => item.Changed)}\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return Invalid(exception.Message);
        }
    }

    private static int RuleNumber(string value)
    {
        if (value.Length != 6
            || !int.TryParse(
                value.AsSpan(3),
                NumberStyles.None,
                CultureInfo.InvariantCulture,
                out var number))
        {
            throw new InvalidOperationException($"Engine emitted an invalid rule ID: {value}");
        }

        return number;
    }

    private static CommandResult Invalid(string message) =>
        new(false, string.Empty, $"GOLDEN_RECORD_INVALID {message}\n");
}
