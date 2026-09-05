using System.Reflection;

namespace StrataLint.ArchitectureTests;

internal static class SiblingTestAssemblyLoader
{
    private const string CurrentProjectName = "StrataLint.ArchitectureTests";

    internal static Assembly Load(string assemblyName)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(assemblyName);

        var repositoryRoot = RepositoryLayout.FindRoot();
        var currentProjectDirectory = Path.Combine(
            repositoryRoot,
            "tools",
            "tests",
            CurrentProjectName);
        var currentAssemblyDirectory = Path.GetDirectoryName(
            typeof(SiblingTestAssemblyLoader).Assembly.Location)
            ?? throw new InvalidOperationException(
                $"Cannot determine the output directory for {CurrentProjectName}.");
        var outputPath = Path.GetRelativePath(
            currentProjectDirectory,
            currentAssemblyDirectory);
        var candidate = Path.GetFullPath(Path.Combine(
            repositoryRoot,
            "tools",
            "tests",
            assemblyName,
            outputPath,
            assemblyName + ".dll"));

        if (File.Exists(candidate))
        {
            return Assembly.LoadFrom(candidate);
        }

        throw new FileNotFoundException(
            $"Could not load test assembly {assemblyName}.{Environment.NewLine}"
            + $"Attempted paths:{Environment.NewLine}{candidate}",
            candidate);
    }
}
