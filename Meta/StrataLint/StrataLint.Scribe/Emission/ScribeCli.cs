using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeCli
{
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
        if (command == "artifact-inventory")
        {
            if (arguments.Count != 2
                || !string.Equals(arguments[1], "--null", StringComparison.Ordinal))
            {
                error.WriteLine(Usage);
                return 2;
            }

            foreach (var artifact in GeneratedArtifactInventory.All)
            {
                output.Write(artifact.Path);
                output.Write('\0');
            }

            return 0;
        }

        if (command == "describe-report")
        {
            var json = arguments.Count == 2
                && string.Equals(arguments[1], "--json", StringComparison.Ordinal);
            if (arguments.Count is < 1 or > 2 || (arguments.Count == 2 && !json))
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
                    reportMaterial);
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
            || command is not ("emit" or "catalog" or "emit-values" or "filemap")
            || (arguments.Count == 2 && !check))
        {
            error.WriteLine(Usage);
            return 2;
        }

        try
        {
            var repositoryRoot = FindRepositoryRoot(workingDirectory);
            if (command == "catalog")
            {
                return AnchorCatalogEmitter.Emit(repositoryRoot, check, output, error);
            }

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
        "usage: dotnet run --project Meta/StrataLint/StrataLint.Scribe -- "
        + "emit|catalog|emit-values|filemap [--check] | artifact-inventory --null "
        + "| describe-report [--json]";

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
