using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class LibraryNoteTests
{
    [Fact]
    public void LibraryReferenceOwnsTheD5LAddressAndLiteratureAnchor()
    {
        var reference = LibraryNoteRef.Create("D5/L/sos1957threegap");
        var provenance = DescribeProvenance.LiteratureAttested(reference);

        Assert.Equal("D5/L/sos1957threegap", reference.Value);
        Assert.Equal("sos1957threegap", reference.BibKey.Value);
        Assert.Equal("lit/sos1957threegap", reference.Anchor.CanonicalString);
        Assert.Equal(DescribeProvenanceKind.LiteratureAttested, provenance.Kind);
        Assert.Same(reference, provenance.LiteratureReference);
        Assert.Throws<ArgumentException>(() => LibraryNoteRef.Create("D5/S1/Phase/Basic"));
        Assert.Throws<ArgumentException>(() => LibraryNoteRef.Create("D5/L/Sos1957threegap"));
    }

    [Fact]
    public void LibraryCatalogParsesCanonicalMetadataFromTheNoteOnly()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sos1957threegap.md"] = Note(
                    "sos1957threegap",
                    "On the three gap theorem",
                    "10.1007/BF01389053"),
            },
            root =>
            {
                var catalog = LibraryNoteCatalog.Load(root);
                var note = Assert.Single(catalog.Notes);
                Assert.Equal("sos1957threegap", note.BibKey.Value);
                Assert.Equal("On the three gap theorem", note.Title);
                Assert.Equal("10.1007/BF01389053", note.Doi!.Value);
                Assert.Equal("D5/S1/Phase/Basic", Assert.Single(note.StrataTouched).Value);
            });
    }

    [Fact]
    public void LibraryCatalogRejectsMalformedOrDuplicateDois()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sos1957threegap.md"] = Note(
                    "sos1957threegap",
                    "Malformed DOI",
                    "https://doi.org/10.1007/BF01389053"),
            },
            root => Assert.Throws<FormatException>(() => LibraryNoteCatalog.Load(root)));

        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sos1957threegap.md"] = Note(
                    "sos1957threegap",
                    "First title",
                    "10.1007/BF01389053"),
                ["slater1967gaps.md"] = Note(
                    "slater1967gaps",
                    "Second title",
                    "10.1007/bf01389053"),
            },
            root =>
            {
                var error = Assert.Throws<FormatException>(() => LibraryNoteCatalog.Load(root));
                Assert.Contains("duplicate DOI", error.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void LibraryCatalogRejectsBibkeyThatDisagreesWithItsPath()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sos1957threegap.md"] = Note(
                    "slater1967gaps",
                    "Wrong key",
                    "10.1007/BF01389053"),
            },
            root => Assert.Throws<FormatException>(() => LibraryNoteCatalog.Load(root)));
    }

    [Fact]
    public void LibraryCatalogRejectsMalformedTaskTriage()
    {
        WithCatalog(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["sos1957threegap.md"] = Note(
                    "sos1957threegap",
                    "Malformed task",
                    "10.1007/BF01389053",
                    triage: "task(garbage)"),
            },
            root => Assert.Throws<FormatException>(() => LibraryNoteCatalog.Load(root)));
    }

    private static void WithCatalog(
        IReadOnlyDictionary<string, string> notes,
        Action<string> assertion)
    {
        var root = Path.Combine(Path.GetTempPath(), "stratalint-library-" + Guid.NewGuid().ToString("N"));
        var directory = Path.Combine(root, "Library", "notes");
        Directory.CreateDirectory(directory);
        try
        {
            foreach (var (name, content) in notes)
            {
                File.WriteAllText(Path.Combine(directory, name), content, new UTF8Encoding(false, true));
            }

            assertion(root);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    private static string Note(
        string bibkey,
        string title,
        string doi,
        string triage = "anchor") =>
        "---\n"
        + $"bibkey: {bibkey}\n"
        + $"title: {title}\n"
        + $"doi: {doi}\n"
        + "claim: Gap lengths for irrational rotations.\n"
        + "strata_touched:\n"
        + "  - D5/S1/Phase/Basic\n"
        + "license: citation-only\n"
        + $"triage: {triage}\n"
        + "---\n";
}
