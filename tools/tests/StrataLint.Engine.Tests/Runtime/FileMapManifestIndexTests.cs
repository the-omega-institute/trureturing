using System.Collections.Immutable;

namespace StrataLint.Engine.Tests;

public sealed class FileMapManifestIndexTests
{
    [Fact]
    public void MatchesAgreeWithEntryScanAcrossRootsWildcardsAndExclusions()
    {
        string[] patterns = ["Meta/**/*.json", "**", "Root[1]+(x).json", "Meta/*/part*.json",
            "*/data.json", "**/*.json", "Meta", "M*ta/**/*.json", "*.json", "Other/**",
            ".hidden/**/*.json", "Meta/**/*.json", "meta/**/*.json", "Prefix**/data.json"];
        var entries = patterns.Select(pattern => Entry(pattern,
            pattern == "Meta/**/*.json" ? ["Meta/private/**", "Meta/skip.json"] : [])).ToImmutableArray();
        var manifest = Manifest(entries);
        string[] roots = ["Meta", "meta", "Other", "Unknown", ".hidden", "Prefix", "PrefixNested", ""];
        string[] suffixes = ["", "/", "/data.json", "/deep/data.json", "/deep/part1.json", "/skip.json",
            "/private/data.json", "/private/nested/data.json", "/data.json\n", "/data.JSON", "//data.json"];
        var paths = roots.SelectMany(root => suffixes.Select(suffix => root + suffix))
            .Concat(["Root[1]+(x).json", "Root1x.json", "else.json", "Meta\\data.json", "Meta/data.json/extra"]);

        foreach (var path in paths)
            Assert.Equal(entries.Where(entry => entry.Matches(path)), manifest.Match(path));
    }

    [Fact]
    public void InterleavedGlobalMatchesKeepDeclarationOrderAndDuplicates()
    {
        var entry = Entry("Meta/**/*.json");
        var manifest = Manifest([Entry("**/*.json"), entry, Entry("M*ta/*.json"), entry, Entry("Meta/data.json")]);

        Assert.Equal(manifest.Entries, manifest.Match("Meta/data.json"));
        Assert.Equal(new[] { manifest.Entries[0], manifest.Entries[2] }, manifest.Match("Mata/data.json"));
        Assert.Empty(manifest.Match("Else/data.txt"));
    }

    [Fact]
    public void EmptyAndUnknownRootsRetainGlobalPatterns()
    {
        var manifest = Manifest([Entry("Meta/**"), Entry("**/data.json"), Entry("*")]);

        Assert.Equal(new[] { manifest.Entries[1] }, manifest.Match("Unknown/data.json"));
        Assert.Equal(new[] { manifest.Entries[2] }, manifest.Match(""));
        Assert.Equal(new[] { manifest.Entries[1], manifest.Entries[2] }, manifest.Match("data.json"));
        Assert.Empty(Manifest([]).Match("Meta/data.json"));
    }

    [Fact]
    public void NullInputKeepsTheEntryMatcherDiagnostic()
    {
        Assert.Empty(Manifest([]).Match(null!));
        foreach (var pattern in new[] { "Meta/data.json", "Meta/**", "**" })
        {
            var exception = Assert.Throws<ArgumentNullException>(() => Manifest([Entry(pattern)]).Match(null!));
            Assert.Equal("input", exception.ParamName);
        }
    }

    [Fact]
    public void SeparateManifestsKeepTheirOwnExclusionsDuringConcurrentReads()
    {
        var original = Manifest([Entry("Meta/**", ["Meta/private/**"])]);
        var replacement = Manifest([Entry("Meta/**"), Entry("Other/**")]);
        Parallel.For(0, 64, _ =>
        {
            Assert.Empty(original.Match("Meta/private/data.json"));
            Assert.Single(replacement.Match("Meta/private/data.json"));
            Assert.Empty(original.Match("Other/data.json"));
            Assert.Single(replacement.Match("Other/data.json"));
        });
    }

    private static FileMapEntry Entry(string pattern, ImmutableArray<string> exclude = default) =>
        new(pattern, FileMapKind.Data, FileMapAdmissionPlane.Content, "none", ["reader"],
            ["SnapshotDecoder"], false, "none", null, "committed-source", null, null, exclude: exclude);

    private static FileMapManifest Manifest(ImmutableArray<FileMapEntry> entries) =>
        new(new FileMapResidencePolicy("FIXTURE", "registered", 0, "closed"), entries,
            ImmutableDictionary<ArtifactKindId, ArtifactPolicy>.Empty);
}
