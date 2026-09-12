using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapSymlinkTests
{
    [Fact]
    public void EquivalentTomlTablesDescribeTheSameLink()
    {
        var inline = Manifest(".codex/skills", "../skills", "directory");
        var subtable = inline.Replace("symlink = { target = \"../skills\", kind = \"directory\" }",
            "[files.symlink]\ntarget = \"../skills\"\nkind = \"directory\"", StringComparison.Ordinal);
        var inlineBytes = Encoding.UTF8.GetBytes(inline);
        var tableBytes = Encoding.UTF8.GetBytes(subtable);
        Assert.Equal(Assert.Single(FileMapLoader.Parse(inlineBytes, "inline.toml").Entries).Symlink,
            Assert.Single(FileMapLoader.Parse(tableBytes, "table.toml").Entries).Symlink);
        Assert.Equal(Assert.Single(FileMapSymlinkPolicy.Parse(inlineBytes, "inline.toml")),
            Assert.Single(FileMapSymlinkPolicy.Parse(tableBytes, "table.toml")));
    }

    [Fact]
    public void HistoricalSchemaTwoNeedsOnlyItsOwnSymlinkFields()
    {
        var current = Manifest("AGENTS.md", "CLAUDE.md", "file");
        var historical = current.Replace("schema_version = 3", "schema_version = 2", StringComparison.Ordinal);
        var begin = historical.IndexOf("[evidence.", StringComparison.Ordinal);
        var end = historical.IndexOf("[residence_policy]", StringComparison.Ordinal);
        historical = historical.Remove(begin, end - begin);
        Assert.Equal("CLAUDE.md", Assert.Single(FileMapSymlinkPolicy.Parse(Encoding.UTF8.GetBytes(historical), "historical")).Target);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(Encoding.UTF8.GetBytes(historical), "current"));
    }

    [Theory]
    [InlineData("AGENTS.md", "CLAUDE.md", "file", "CLAUDE.md")]
    [InlineData(".codex/skills", "../skills", "directory", "skills")]
    public void FileAndDirectoryDeclarationsDriveTheProjection(string path, string target, string kind, string resolved)
    {
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes(Manifest(path, target, kind)), "fixture.toml");
        var link = Assert.Single(manifest.Entries).Symlink;
        Assert.NotNull(link);
        Assert.Equal(resolved, link.ResolvedTarget);
        Assert.Contains($"[{path} | program] --symlink({kind})--> {target}",
            Encoding.UTF8.GetString(FileMapProjectionWriter.Write(manifest).AsSpan()), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("AGENTS.md", "../CLAUDE.md", "file")]
    [InlineData("AGENTS.md", "/CLAUDE.md", "file")]
    [InlineData("AGENTS.md", "./CLAUDE.md", "file")]
    [InlineData("AGENTS.md", "folder/../CLAUDE.md", "file")]
    [InlineData("AGENTS.md", "C:/CLAUDE.md", "file")]
    [InlineData("AGENTS.md", "CLAUDE.md", "unknown")]
    [InlineData("*.md", "CLAUDE.md", "file")]
    [InlineData("Meta/FILEMAP.toml", "rules.toml", "file")]
    [InlineData("Meta", "rules", "directory")]
    [InlineData(".lake", "cache", "directory")]
    [InlineData("alias", ".git/config", "file")]
    [InlineData("skills/alias", "..", "directory")]
    [InlineData("alias", "alias/child", "directory")]
    public void InvalidDeclarationsAreRejectedByBothConsumers(string path, string target, string kind)
    {
        var bytes = Encoding.UTF8.GetBytes(Manifest(path, target, kind));
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "fixture.toml"));
        Assert.ThrowsAny<FormatException>(() => FileMapSymlinkPolicy.Parse(bytes, "fixture.toml"));
    }

    [Theory]
    [InlineData("symlink = true")]
    [InlineData("symlink = { target = \"CLAUDE.md\" }")]
    [InlineData("symlink = { target = \"CLAUDE.md\", kind = \"file\", follow = true }")]
    public void UnknownOrIncompleteLinkShapeIsRejected(string declaration)
    {
        var source = Manifest("AGENTS.md", "CLAUDE.md", "file").Replace(
            "symlink = { target = \"CLAUDE.md\", kind = \"file\" }", declaration, StringComparison.Ordinal);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));
    }

    [Fact]
    public void DeclaredAliasCannotAlsoMatchABroaderEntry()
    {
        var source = Manifest(".codex/**", "../skills", "directory")
            .Replace("symlink = { target = \"../skills\", kind = \"directory\" }\n", "", StringComparison.Ordinal)
            + Manifest(".codex/skills", "../skills", "directory").Split("[[files]]", StringSplitOptions.None)[1]
                .Insert(0, "[[files]]");
        var bytes = Encoding.UTF8.GetBytes(source);
        Assert.ThrowsAny<FormatException>(() => FileMapLoader.Parse(bytes, "fixture.toml"));
        Assert.ThrowsAny<FormatException>(() => FileMapSymlinkPolicy.Parse(bytes, "fixture.toml"));
    }

    private static string Manifest(string path, string target, string kind) => $$"""
        schema_version = 3
        [evidence.artifact_kinds.json]
        profile = "structured-json"
        selectors = ["result"]
        path_selectors = ["formal"]

        [residence_policy]
        case_id = "RESIDENCE-EPOCH"
        desired = "data-must-live-outside-tools"
        known_violation_count = 0
        status = "closed"
        [[files]]
        pattern = "{{path}}"
        kind = "program"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["agent"]
        verified_by = ["repository-policy"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        symlink = { target = "{{target}}", kind = "{{kind}}" }
        """ + "\n";
}
