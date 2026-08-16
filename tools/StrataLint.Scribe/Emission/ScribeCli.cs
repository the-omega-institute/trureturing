using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeCli
{
    internal sealed record EmissionOptions(
        bool Check,
        string? BaseRevision,
        string? ChangesFile,
        string? ProducerPathsFile);

    private static readonly ImmutableHashSet<string> EmissionCommands =
        ImmutableHashSet.Create(StringComparer.Ordinal, "emit", "emit-values", "filemap");

    public static ImmutableArray<string> ImplementedCommands { get; } =
        ["describe-report", .. EmissionCommands.Order(StringComparer.Ordinal), "projections"];

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
        LeanAxiomReport? leanReport)
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

        if (!EmissionCommands.Contains(command)
            || !TryParseEmissionOptions(arguments.Skip(1), out var emissionOptions)
            || command == "filemap" && emissionOptions.BaseRevision is not null)
        {
            error.WriteLine(Usage);
            return 2;
        }

        try
        {
            var repositoryRoot = FindRepositoryRoot(workingDirectory);
            var delta = emissionOptions.BaseRevision is null
                ? null
                : ScribeDeltaInputLoader.Load(
                    repositoryRoot,
                    emissionOptions.BaseRevision,
                    emissionOptions.ChangesFile!,
                    emissionOptions.ProducerPathsFile!);
            if (command == "emit-values")
            {
                return delta is null
                    ? ValuesEmitter.Emit(repositoryRoot, emissionOptions.Check, output, error)
                    : ValuesEmitter.Emit(repositoryRoot, emissionOptions.Check, output, error, delta);
            }

            if (command == "filemap")
            {
                return FileMapEmitter.Emit(repositoryRoot, emissionOptions.Check, output, error);
            }

            if (delta is null)
            {
                return leanReport is null
                    ? ScribeEmitter.Emit(repositoryRoot, emissionOptions.Check, output, error)
                    : ScribeEmitter.Emit(repositoryRoot, emissionOptions.Check, output, error, leanReport);
            }

            return leanReport is null
                ? ScribeEmitter.Emit(repositoryRoot, emissionOptions.Check, output, error, delta)
                : ScribeEmitter.Emit(
                    repositoryRoot,
                    emissionOptions.Check,
                    output,
                    error,
                    leanReport,
                    delta);
        }
        catch (Exception exception) when (
            exception is IOException
                or UnauthorizedAccessException
                or ArgumentException
                or FormatException
                or InvalidOperationException
                or TimeoutException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }

    private const string Usage =
        "usage: dotnet run --project tools/StrataLint.Scribe -- "
        + "emit|emit-values|filemap [--check] "
        + "[--base SHA --changes-file FILE --producer-paths-file FILE] "
        + "| describe-report [--json] [--check] "
        + "| projections --check --report <file>";

    internal static bool TryParseEmissionOptions(
        IEnumerable<string> rawOptions,
        out EmissionOptions options)
    {
        var values = rawOptions.ToArray();
        var check = false;
        string? baseRevision = null;
        string? changesFile = null;
        string? producerPathsFile = null;
        for (var index = 0; index < values.Length; index++)
        {
            switch (values[index])
            {
                case "--check" when !check:
                    check = true;
                    break;
                case "--base" when baseRevision is null && index + 1 < values.Length:
                    baseRevision = values[++index];
                    break;
                case "--changes-file" when changesFile is null && index + 1 < values.Length:
                    changesFile = values[++index];
                    break;
                case "--producer-paths-file" when producerPathsFile is null && index + 1 < values.Length:
                    producerPathsFile = values[++index];
                    break;
                default:
                    options = null!;
                    return false;
            }
        }

        var hasDelta = baseRevision is not null || changesFile is not null || producerPathsFile is not null;
        if (hasDelta && (!check
                || baseRevision is null
                || changesFile is null
                || producerPathsFile is null))
        {
            options = null!;
            return false;
        }

        options = new EmissionOptions(check, baseRevision, changesFile, producerPathsFile);
        return true;
    }

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
