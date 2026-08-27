using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeCli
{
    private static readonly ImmutableHashSet<string> EmissionCommands =
        ImmutableHashSet.Create(StringComparer.Ordinal, "emit", "emit-values", "filemap");

    public static ImmutableArray<string> ImplementedCommands { get; } =
    [
        "describe-report",
        .. EmissionCommands.Order(StringComparer.Ordinal),
        "markdown-check",
        "projections",
    ];

    public static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error) =>
        Run(arguments, workingDirectory, output, error, leanReport: null);

    internal static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error,
        TextReader input) =>
        Run(arguments, workingDirectory, output, error, leanReport: null, input);

    internal static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport? leanReport,
        TextReader? input = null)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentException.ThrowIfNullOrWhiteSpace(workingDirectory);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        var command = arguments.Count == 0 ? string.Empty : arguments[0];
        if (command == "projections")
        {
            if (arguments.Count != 4
                || !string.Equals(arguments[1], "--check", StringComparison.Ordinal)
                || !string.Equals(arguments[2], "--report", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[3]))
            {
                error.WriteLine(Usage);
                return 2;
            }

            try
            {
                var repositoryRoot = FindRepositoryRoot(workingDirectory);
                var report = leanReport ?? LeanCompiledArtifactReports.ReadRepository(
                    repositoryRoot,
                    arguments[3]);
                var findings = StatementProjectionReconciliation.Check(
                    repositoryRoot,
                    DeclarationCatalog.Create(report));
                foreach (var finding in findings)
                {
                    error.WriteLine(finding);
                }
                return findings.IsEmpty ? 0 : 1;
            }
            catch (Exception exception) when (
                exception is IOException
                    or UnauthorizedAccessException
                    or ArgumentException
                    or FormatException
                    or InvalidOperationException)
            {
                error.WriteLine(exception.Message);
                return 2;
            }
        }

        if (command == "markdown-check")
        {
            if (arguments.Count != 5
                || !string.Equals(arguments[1], "--report", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[2])
                || !string.Equals(arguments[3], "--paths-from", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[4]))
            {
                error.WriteLine(Usage);
                return 2;
            }

            try
            {
                var repositoryRoot = FindRepositoryRoot(workingDirectory);
                var report = leanReport ?? LeanCompiledArtifactReports.ReadRepository(
                    repositoryRoot,
                    arguments[2]);

                // The caller owns the diff: git references stay in the workflow, and this
                // verb judges exactly the paths it is handed.
                var scope = new MarkdownFormulaScope(
                    repositoryRoot,
                    ReadPaths(arguments[4], input));
                return ScribeEmitter.CheckMarkdown(repositoryRoot, output, error, report, scope);
            }
            catch (Exception exception) when (
                exception is IOException
                    or UnauthorizedAccessException
                    or ArgumentException
                    or FormatException
                    or InvalidOperationException)
            {
                error.WriteLine(exception.Message);
                return 2;
            }
        }

        if (command == "describe-report")
        {
            var options = arguments.Skip(1).ToArray();
            var json = options.Contains("--json", StringComparer.Ordinal);
            var describeCheck = options.Contains("--check", StringComparer.Ordinal);
            if (options.Length > 2
                || options.Distinct(StringComparer.Ordinal).Count() != options.Length
                || options.Any(static option => option is not ("--json" or "--check")))
            {
                error.WriteLine(Usage);
                return 2;
            }

            try
            {
                var repositoryRoot = FindRepositoryRoot(workingDirectory);
                var reportMaterial = leanReport
                    ?? LeanCompiledArtifactReports.InspectRepository(repositoryRoot);
                var report = DescribeReport.Build(
                    repositoryRoot,
                    DocumentDefinitions.All.Select(static definition => definition.Document),
                    reportMaterial,
                    validateContentGovernance: describeCheck);
                output.Write(json
                    ? DescribeReportWriter.WriteJson(report)
                    : DescribeReportWriter.WriteText(report));
                return report.RedFindings.IsEmpty ? 0 : 1;
            }
            catch (Exception exception) when (
                exception is IOException
                    or UnauthorizedAccessException
                    or ArgumentException
                    or FormatException
                    or InvalidOperationException)
            {
                error.WriteLine(exception.Message);
                return 2;
            }
        }

        var check = arguments.Count == 2
            && string.Equals(arguments[1], "--check", StringComparison.Ordinal);
        if (arguments.Count is < 1 or > 2
            || !EmissionCommands.Contains(command)
            || (arguments.Count == 2 && !check))
        {
            error.WriteLine(Usage);
            return 2;
        }

        try
        {
            var repositoryRoot = FindRepositoryRoot(workingDirectory);
            if (command == "emit-values")
            {
                return ValuesEmitter.Emit(repositoryRoot, check, output, error);
            }

            if (command == "filemap")
            {
                return FileMapEmitter.Emit(repositoryRoot, check, output, error);
            }

            return leanReport is null
                ? ScribeEmitter.Emit(repositoryRoot, check, output, error)
                : ScribeEmitter.Emit(repositoryRoot, check, output, error, leanReport);
        }
        catch (Exception exception) when (
            exception is IOException or UnauthorizedAccessException or ArgumentException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }

    private const string Usage =
        "usage: dotnet run --project tools/StrataLint.Scribe -- "
        + "emit|emit-values|filemap [--check] | describe-report [--json] [--check] "
        + "| projections --check --report <file> "
        + "| markdown-check --report <file> --paths-from <file|->";

    /// <summary>
    /// The paths to judge. `-` reads them from standard input, which keeps the change's
    /// paths out of a temporary file the caller would then have to clean up.
    /// </summary>
    private static ImmutableArray<string> ReadPaths(string pathsFile, TextReader? input) =>
        MarkdownFormulaScope.ParsePaths(string.Equals(pathsFile, "-", StringComparison.Ordinal)
            ? (input ?? Console.In).ReadToEnd()
            : File.ReadAllText(pathsFile));

    private static string FindRepositoryRoot(string workingDirectory)
    {
        for (var current = new DirectoryInfo(Path.GetFullPath(workingDirectory));
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException(
            "Could not locate a repository root containing global.json and Blueprint/.");
    }
}
