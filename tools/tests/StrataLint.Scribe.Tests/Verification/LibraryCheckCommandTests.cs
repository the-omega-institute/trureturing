using System.Reflection;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class LibraryCheckCommandTests
{
    private const string Formal = "D5/S0/Synthetic/LibraryCheck.lean";

    [Theory]
    [InlineData("valid", 0, "library: findings=0")]
    [InlineData("bad-format", 1, "invalid-library-note")]
    [InlineData("dangling-module", 1, "dangling-library-gid")]
    [InlineData("dangling-declaration", 1, "dangling-library-gid")]
    [InlineData("dangling-triage", 1, "dangling-library-gid")]
    [InlineData("dangling-literature", 1, "dangling-literature-reference")]
    [InlineData("missing-locator", 1, "incomplete-library-locator")]
    [InlineData("problem-source", 1, "problem-source-mismatch")]
    [InlineData("missing-report", 2, "missing-report.json")]
    public void ChecksOnlyLibraryObligationsWithRealReferenceEvidence(string scenario, int expected, string diagnostic)
    {
        using var root = new TemporaryRoot();
        SyntheticScribeRepository.WriteInputs(root.Path, Definition());
        Write("global.json", "{}\n");
        Write(Formal, "namespace D5.S0.Synthetic.LibraryCheck\n");
        Write("Blueprint/D5/S0/Synthetic/Unrelated.md", "$$u_{n}_{i}$$\n");
        var touched = scenario == "dangling-module" ? "D5/S0/Synthetic/Missing"
            : scenario == "dangling-declaration" ? "D5/S0/Synthetic/LibraryCheck.missing"
            : "D5/S0/Synthetic/LibraryCheck";
        if (scenario != "dangling-literature") Write("Library/notes/probe2026note.md", scenario == "bad-format"
            ? "not canonical metadata\n"
            : "---\nbibkey: probe2026note\nauthors: A. Author\nyear: 2026\ntitle: Library fixture\n"
              + "doi: 10.1007/BF01389053\nclaim: A library reference.\nstrata_touched:\n  - " + touched
              + "\nlicense: citation-only\ntriage: "
              + (scenario == "dangling-triage" ? "task(D5/S0/Synthetic/Missing)" : "anchor") + "\n---\n"
              + (scenario == "missing-locator" ? "" : "\n## Verified locator\n\n10.1007/BF01389053, source statement.\n"));
        if (scenario == "problem-source") Write("Problems/sample-problem.md",
            "---\nslug: sample-problem\nbibkey: probe2026note\ndoi: 10.48550/arXiv.2305.08349\ntriage: theorem\n"
            + "motivation_gids:\n  - D5/S0/Synthetic/LibraryCheck\n---\n\n# A problem\n\n"
            + string.Join("\n", new[] { "Problem", "Motivation", "Gap", "Route", "Falsifier", "Evidence", "Triage", "ASSUMED-UNVERIFIED" }
                .Select(heading => "## " + heading + "\n\nA fixture statement.\n")));
        var output = new StringWriter();
        var error = new StringWriter();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            { [Formal] = new([], []) });
        var exit = scenario == "missing-report"
            ? ScribeCli.Run(new Documents(), ["library-check", "--report", "missing-report.json"], root.Path, output, error)
            : ScribeCli.Run(new Documents(), ["library-check", "--report", "fixture.json"], root.Path, output, error, report);
        Assert.True(exit == expected, output.ToString() + error);
        Assert.Contains(diagnostic, output.ToString() + error, StringComparison.Ordinal);

        void Write(string path, string text) => TemporaryFileSystem.File.WriteAllText(root.Resolve(path), text);
    }

    public static DocumentDefinition Definition() => DocumentDefinition.Create(
        ScribeDocument.Create(
            DefinitionDsl.Header("D5/S0/Synthetic/LibraryCheck", "Library command fixture.", Anchor.ParseCanonical("lit/probe2026note")),
            DefinitionDsl.H("Library"), DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Library fixture.")))),
        "Blueprint/D5/S0/Synthetic/LibraryCheck.scribe.cs");

    private sealed class Documents : Assembly
    {
        public override Type[] GetTypes() => [typeof(Document)];
    }

    private sealed class Document : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => Definition();
    }
}
