using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeCli
{
    private static readonly ImmutableHashSet<string> EmissionCommands =
        ImmutableHashSet.Create(StringComparer.Ordinal, "emit", "emit-values", "filemap");

    public static ImmutableArray<string> ImplementedCommands { get; } =
    [
        "content-check",
        "describe-report",
        .. EmissionCommands.Order(StringComparer.Ordinal),
        "markdown-check",
        "projections",
        "resources",
        "resources release",
        "resources verify-release",
        "scripts",
    ];

    public static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error) => Run(arguments, workingDirectory, output, error, leanReport: null);

    internal static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error,
        TextReader input) => Run(arguments, workingDirectory, output, error, leanReport: null, input);

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
        if (command == "resources")
        {
            return ScribeResourceCommands.Run(arguments, workingDirectory,
                () => FindRepositoryRoot(workingDirectory), output, error);
        }

        if (command == "scripts")
        {
            try
            {
                return ScribeScriptVerifyCommands.Run(
                    arguments,
                    FindRepositoryRoot(workingDirectory),
                    input,
                    output,
                    error);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
                or ArgumentException or FormatException or InvalidOperationException)
            {
                error.WriteLine(exception.Message);
                return 2;
            }
        }

        if (command is "content-check" or "markdown-check")
        {
            if (arguments.Count == 3 && arguments[1] == "--report")
            {
                error.WriteLine($"MissingPathsManifest: {command} requires --paths-from <file|->");
                return 2;
            }
            if (arguments.Count != 5 || arguments[1] != "--report"
                || string.IsNullOrWhiteSpace(arguments[2]) || arguments[3] != "--paths-from"
                || string.IsNullOrWhiteSpace(arguments[4]))
            {
                error.WriteLine(Usage);
                return 2;
            }
            try
            {
                var root = FindRepositoryRoot(workingDirectory);
                var report = leanReport ?? LeanCompiledArtifactReports.ReadRepositoryFiles(root, arguments[2]);
                if (command == "content-check")
                {
                    var exit = Run(["projections", "--check", "--report", arguments[2]],
                        workingDirectory, output, error, report);
                    if (exit != 0) return exit;
                }
                return ScribeContentChecks.Run(root, ReadPaths(arguments[4], input), report,
                    command == "content-check", output, error);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
                or ArgumentException or FormatException or InvalidOperationException)
            {
                error.WriteLine(exception.Message);
                return 2;
            }
        }

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
                var report = leanReport ?? LeanCompiledArtifactReports.ReadRepositoryFiles(
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

        if (command == "describe-report")
        {
            var options = arguments.Skip(5).ToArray();
            var json = options.Contains("--json", StringComparer.Ordinal);
            var describeCheck = options.Contains("--check", StringComparer.Ordinal);
            if (arguments.Count is < 5 or > 7 || arguments[1] != "--scribe-pack"
                || string.IsNullOrWhiteSpace(arguments[2]) || arguments[3] != "--scribe-pack-digest"
                || !System.Text.RegularExpressions.Regex.IsMatch(arguments[4], "^[0-9a-f]{64}$")
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
                    ?? LeanCompiledArtifactReports.ReadRepositoryFiles(repositoryRoot);
                var pack = ScribeResourcePack.Open(arguments[2]);
                if (pack.Manifest.TotalSha256 != arguments[4])
                    throw new FormatException("ScribePackDigestMismatch: the pack digest does not match");
                var definitions = pack.ReadAll();
                var report = DescribeReport.Build(
                    repositoryRoot,
                    definitions.Select(static definition => definition.Document),
                    reportMaterial,
                    validateContentGovernance: describeCheck, validateSourceFiles: false);
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

        if (command == "emit" && arguments.Count is (3 or 4)
            && arguments[1] == "--paths-from"
            && !string.IsNullOrWhiteSpace(arguments[2])
            && (arguments.Count == 3 || arguments[3] == "--check"))
        {
            try
            {
                var repositoryRoot = FindRepositoryRoot(workingDirectory);
                var paths = ReadPaths(arguments[2], input);
                if (paths.IsEmpty)
                {
                    output.WriteLine("emitted: 0 changed blueprint(s)");
                    return 0;
                }
                return ScribeEmitter.EmitPaths(
                    repositoryRoot,
                    paths,
                    arguments.Count == 4,
                    output,
                    error,
                    () => leanReport ?? LeanCompiledArtifactReports.ReadRepositoryFiles(repositoryRoot));
            }
            catch (Exception exception) when (
                exception is IOException or UnauthorizedAccessException or ArgumentException
                    or FormatException or InvalidOperationException)
            {
                error.WriteLine(exception.Message);
                return 2;
            }
        }

        if (command == "emit")
        {
            error.WriteLine(arguments.Count == 1 || (arguments.Count == 2 && arguments[1] == "--check")
                ? "MissingPathsManifest: emit requires --paths-from <file|->" : Usage);
            return 2;
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

            error.WriteLine(Usage);
            return 2;
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
        + "emit-values|filemap [--check] | emit --paths-from <file|-> [--check] | describe-report --scribe-pack <file> --scribe-pack-digest <hex64> [--json] [--check] "
        + "| content-check --report <file> --paths-from <file|-> "
        + "| projections --check --report <file> "
        + "| markdown-check --report <file> --paths-from <file|-> "
        + "| resources pack --out <file> | resources verify --pack <file> "
        + "| resources release --out <directory> "
        + "| resources verify-release --dir <directory> [--total-sha256 <digest>] "
        + "| scripts verify [--paths-from <file|->]";

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
