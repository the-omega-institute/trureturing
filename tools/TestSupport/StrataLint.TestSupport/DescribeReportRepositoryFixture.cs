using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.TestSupport;

internal static class DescribeReportRepositoryFixture
{
    internal static void WithRepository(
        Action<string> assertion,
        string doi = "10.1007/BF01389053")
    {
        var root = Path.Combine(Path.GetTempPath(), "stratalint-report-" + Guid.NewGuid().ToString("N"));
        var formalPath = Path.Combine(root, "D5", "S1", "Phase", "Basic.lean");
        var notes = Path.Combine(root, "Library", "notes");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(formalPath)!);
        TemporaryFileSystem.Directory.CreateDirectory(notes);
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "Blueprint"));
        var repository = RepositoryAccessor.Discover(
            RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation);
        var projectionDirectory = Path.Combine(root, "Golden", "Projection");
        TemporaryFileSystem.Directory.CreateDirectory(projectionDirectory);
        foreach (var source in repository.EnumerateFiles(
                     RepositoryRelativePath.Create("Golden/Projection"),
                     "*.json"))
        {
            repository.CopyTo(
                source,
                Path.Combine(projectionDirectory, Path.GetFileName(source.Value)),
                overwrite: true);
        }
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, "global.json"), "{}\n", new UTF8Encoding(false, true));
        TemporaryFileSystem.File.WriteAllText(
            formalPath,
            "/-- Formula x = y in a Lean docstring. -/\nnamespace D5.S1.Phase\n",
            new UTF8Encoding(false, true));
        WriteNote(
            root,
            "sos1957threegap",
            "On the three gap theorem",
            doi);
        try
        {
            assertion(root);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    internal static void WriteNote(
        string root,
        string bibkey,
        string title,
        string doi)
    {
        var notes = Path.Combine(root, "Library", "notes");
        TemporaryFileSystem.Directory.CreateDirectory(notes);
        TemporaryFileSystem.File.WriteAllText(
            Path.Combine(notes, bibkey + ".md"),
            "---\n"
            + $"bibkey: {bibkey}\n"
            + "authors: Vera T. Sos\n"
            + "year: 1957\n"
            + $"title: {title}\n"
            + $"doi: {doi}\n"
            + "claim: Gap lengths for irrational rotations.\n"
            + "strata_touched:\n"
            + "  - D5/S1/Phase/Basic\n"
            + "license: citation-only\n"
            + "triage: anchor\n"
            + "---\n",
            new UTF8Encoding(false, true));
    }
}
