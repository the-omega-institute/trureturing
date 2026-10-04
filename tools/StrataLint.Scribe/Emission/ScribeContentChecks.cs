using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal static class ScribeContentChecks
{
    internal static int Run(string root, ImmutableArray<string> changedPaths, LeanAxiomReport report,
        bool checkContent, TextWriter output, TextWriter error)
    {
        var selection = ScribeDefinitionSelector.Select(root, changedPaths.Concat(
            changedPaths.Where(static path => path.StartsWith("Blueprint/", StringComparison.Ordinal)
                && path.EndsWith(".md", StringComparison.Ordinal))
                .Select(static path => path[..^3] + ".scribe.cs")));
        if (!selection.IsSuccess)
        {
            error.WriteLine(selection.Failure);
            return 2;
        }
        return StatementProjectionFixtureLoader.WithFreshRepositoryRoot(root, () =>
        {
            var results = ScribeScriptHost.ExecuteBatch(root, selection.Paths);
            var failures = results.Where(static result => !result.IsSuccess).ToArray();
            foreach (var failure in failures) error.WriteLine(failure.Failure);
            if (failures.Length != 0) return 1;
            var definitions = results.Select(static result => ScribeResourceCodec.Decode(
                ScribeResourceCodec.Encode(result.Definition!),
                expectedGid: result.Definition!.Document.Header.Gid.Value,
                expectedSourcePath: result.RelativePath)).ToArray();
            if (checkContent)
            {
                var catalog = DeclarationCatalog.Create(report);
                var library = LibraryNoteCatalog.Inspect(root);
                var problems = ProblemCandidateCatalog.Inspect(root);
                foreach (var definition in definitions)
                {
                    var findings = DescribeReport.Build(root, [definition.Document], report,
                        validateContentGovernance: true, sourcePath: definition.SourcePath,
                        declarationCatalog: catalog, libraryInspection: library, problemInspection: problems).RedFindings;
                    foreach (var finding in findings)
                        error.WriteLine($"describe red code={finding.Code} path={finding.Path} message={finding.Message}");
                    if (!findings.IsEmpty) return 1;
                }
                output.WriteLine(FormattableString.Invariant($"content-check: definitions={definitions.Length}"));
            }
            var scope = new MarkdownFormulaScope(root,
                changedPaths.Concat(definitions.Select(static definition => definition.RelativePath.Value)));
            return ScribeEmitter.CheckMarkdown(root, output, error, report, scope, definitions, scoped: true);
        });
    }
}
