using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeReportTests
{
    private const string FormalPath = "D5/S1/Phase/Basic.lean";

    [Fact]
    public void ReportObservesTitleDerivedIdsAndCrossModuleDeclarationsWithoutBlocking()
    {
        WithRepository(root =>
        {
            var targetDirectory = Path.Combine(root, "D5", "S1", "Scale");
            Directory.CreateDirectory(targetDirectory);
            File.WriteAllText(
                Path.Combine(targetDirectory, "Embedding.lean"),
                "namespace D5.S1.Scale.Embedding\n");
            var document = ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Observation fixture."),
                Heading.Create("Observations"),
                DefinitionDsl.Blocks(DocumentBlock.Describe.Remark(
                    DescribeId.Create("same-title"),
                    Heading.Create("Same title"),
                    DescribeStatement.FromLean(DefinitionDsl.LeanTheorem(
                        "D5/S1/Scale/Embedding.embedding_injective")),
                    DescribeProvenance.RepoDerived(),
                    DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content."))))));

            var report = DescribeReport.Build(root, [document]);

            Assert.Empty(report.RedFindings);
            Assert.Contains(report.Observations, static item =>
                item.Code == "title-derived-id" && item.Path.EndsWith("#describe/same-title", StringComparison.Ordinal));
            Assert.Contains(report.Observations, static item =>
                item.Code == "cross-module-lean-declaration" && item.Path.EndsWith("#describe/same-title", StringComparison.Ordinal));
        });
    }

    [Fact]
    public void JsonReportIsAQueryableClassificationLedgerWithGradedObservations()
    {
        WithRepository(root =>
        {
            var literature = LibraryNoteRef.Create("D5/L/sos1957threegap");
            var document = ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Report fixture."),
                Heading.Create("Report"),
                BlockSequence.Create(
                [
                    Describe("repository", "Repository", DescribeKind.Definition, DescribeProvenance.RepoDerived()),
                    Describe("literature", "Literature", DescribeKind.Theorem, DescribeProvenance.LiteratureAttested(literature)),
                    Describe("candidate", "Candidate", DescribeKind.Lemma, DescribeProvenance.SuspectedNovel()),
                    Describe("open", "Open", DescribeKind.Remark, DescribeProvenance.Unassessed()),
                    new DocumentBlock.Paragraph(InlineSequence.Create(
                    [
                        new Inline.Text(TextRun.Create("Code span `x = y` and Unicode φ.")),
                        new Inline.InlineFormula(new Formula.Phi()),
                    ])),
                    new DocumentBlock.DisplayFormula(new Formula.Phi()),
                ]));

            var report = DescribeReport.Build(root, [document]);
            var first = DescribeReportWriter.WriteJson(report);
            var second = DescribeReportWriter.WriteJson(report);

            Assert.Equal(first, second);
            using var json = JsonDocument.Parse(first);
            var rootElement = json.RootElement;
            Assert.Equal("DESCRIBE-NODES", rootElement.GetProperty("case_id").GetString());
            Assert.Equal("needs-classification", rootElement.GetProperty("status").GetString());
            Assert.Equal(1, rootElement.GetProperty("open_count").GetInt32());
            var stats = rootElement.GetProperty("node_stats");
            Assert.Equal(4, stats.GetProperty("total").GetInt32());
            Assert.Equal(2, stats.GetProperty("formula_content_slots").GetInt32());
            Assert.Equal(1, stats.GetProperty("formula_statements").GetInt32());
            Assert.Single(rootElement.GetProperty("suspected_novel").EnumerateArray());
            Assert.Single(rootElement.GetProperty("unassessed").EnumerateArray());
            Assert.Empty(rootElement.GetProperty("red_findings").EnumerateArray());
            var observationCodes = rootElement.GetProperty("observations")
                .EnumerateArray()
                .Select(static item => item.GetProperty("code").GetString())
                .ToArray();
            Assert.Contains("code-span", observationCodes);
            Assert.Contains("unicode-suspected-formula", observationCodes);
            Assert.Contains("lean-docstring-formula", observationCodes);
            Assert.Contains("online-doi-title-check", observationCodes);
        });
    }

    [Fact]
    public void ClassifiedReportClosesTheUnassessedCountButKeepsNovelCandidatesQueryable()
    {
        WithRepository(root =>
        {
            var document = ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Classified fixture."),
                Heading.Create("Classified"),
                BlockSequence.Create(
                [
                    Describe("candidate", "Candidate", DescribeKind.Proposition, DescribeProvenance.SuspectedNovel()),
                ]));

            var report = DescribeReport.Build(root, [document]);
            var text = DescribeReportWriter.WriteText(report);

            Assert.Equal(0, report.OpenCount);
            Assert.Equal("classified", report.Status);
            Assert.Single(report.SuspectedNovel);
            Assert.Contains("suspected_novel=1", text, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ReportUsesLeanMaterialToRejectAMissingDeclarationSelector()
    {
        WithRepository(root =>
        {
            var document = ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Selector fixture."),
                Heading.Create("Selector"),
                BlockSequence.Create(
                [
                    DocumentBlock.Describe.Theorem(
                        DescribeId.Create("missing-declaration"),
                        Heading.Create("Missing declaration"),
                        LeanDeclarationRef.Create(
                            "D5/S1/Phase/Basic.missing_declaration"),
                        LatexStatement.Create("$x = x$"),
                        DescribeProvenance.RepoDerived(),
                        BlockSequence.Create(
                        [
                            DefinitionDsl.Paragraph(DefinitionDsl.Text("Missing selector fixture.")),
                        ])
                    ),
                ]));
            var leanReport = LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
                {
                    [FormalPath] = new LeanFileReport([], []),
                });

            var report = DescribeReport.Build(root, [document], leanReport);

            Assert.Contains(report.RedFindings, finding => finding.Code == "dangling-gid");
        });
    }

    [Theory]
    [InlineData("not-a-doi", "invalid-doi")]
    [InlineData("10.1007/BF01389053", "duplicate-doi")]
    public void JsonReportRecordsDoiViolationsAsRedFindings(
        string firstDoi,
        string expectedCode)
    {
        WithRepository(
            root =>
            {
                if (expectedCode == "duplicate-doi")
                {
                    WriteNote(
                        root,
                        "slater1967gaps",
                        "Second title",
                        "10.1007/bf01389053");
                }

                var report = DescribeReport.Build(root, []);
                var json = DescribeReportWriter.WriteJson(report);

                Assert.Equal("invalid", report.Status);
                Assert.Contains(report.RedFindings, finding => finding.Code == expectedCode);
                using var document = JsonDocument.Parse(json);
                Assert.Contains(document.RootElement.GetProperty("red_findings").EnumerateArray(), finding =>
                    finding.GetProperty("code").GetString() == expectedCode);
            },
            doi: firstDoi);
    }

    [Fact]
    public void DescribeReportCliReturnsJsonRedAndExitOneForInvalidDoi()
    {
        WithRepository(
            root =>
            {
                var output = new StringWriter();
                var error = new StringWriter();

                var exit = ScribeCli.Run(
                    ["describe-report", "--json"],
                    root,
                    output,
                    error,
                    LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()));

                Assert.Equal(1, exit);
                Assert.Equal(string.Empty, error.ToString());
                using var document = JsonDocument.Parse(output.ToString());
                Assert.Contains(
                    document.RootElement.GetProperty("red_findings").EnumerateArray(),
                    finding => finding.GetProperty("code").GetString() == "invalid-doi");
            },
            doi: "not-a-doi");
    }

    [Fact]
    public void InsertingAPrecedingDescribeDoesNotRenumberExistingNodeIds()
    {
        WithRepository(root =>
        {
            var existing = Describe(
                "existing-claim",
                "Existing",
                DescribeKind.Remark,
                DescribeProvenance.RepoDerived());
            var before = ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Before fixture."),
                Heading.Create("Before"),
                BlockSequence.Create([existing]));
            var after = ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "After fixture."),
                Heading.Create("After"),
                BlockSequence.Create(
                [
                    Describe(
                        "new-claim",
                        "New",
                        DescribeKind.Remark,
                        DescribeProvenance.RepoDerived()),
                    existing,
                ]));

            var beforeId = Assert.Single(DescribeReport.Build(root, [before]).Nodes).NodeId;
            var afterId = Assert.Single(
                DescribeReport.Build(root, [after]).Nodes,
                node => node.Title == "Existing").NodeId;

            Assert.Equal("D5/S1/Phase/Basic#describe/existing-claim", beforeId);
            Assert.Equal(beforeId, afterId);
        });
    }

    private static DocumentBlock.Describe Describe(
        string id,
        string title,
        DescribeKind kind,
        DescribeProvenance provenance)
    {
        var describeId = DescribeId.Create(id);
        var heading = Heading.Create(title);
        var content = DefinitionDsl.Blocks(
            DefinitionDsl.Paragraph(DefinitionDsl.Text("Typed narrative.")));
        var lean = DefinitionDsl.LeanTheorem("D5/S1/Phase/Basic.fixture_claim");
        var latex = LatexStatement.Create("$x = x$");
        return kind switch
        {
            DescribeKind.Definition => DocumentBlock.Describe.Definition(
                describeId, heading, lean, provenance, content),
            DescribeKind.Theorem => DocumentBlock.Describe.Theorem(
                describeId, heading, lean, latex, provenance, content),
            DescribeKind.Proposition => DocumentBlock.Describe.Proposition(
                describeId, heading, lean, latex, provenance, content),
            DescribeKind.Lemma => DocumentBlock.Describe.Lemma(
                describeId, heading, lean, latex, provenance, content),
            DescribeKind.Example => DocumentBlock.Describe.Example(
                describeId, heading, new Formula.Phi(), provenance, content),
            DescribeKind.Remark => DocumentBlock.Describe.Remark(
                describeId,
                heading,
                DescribeStatement.FromFormula(new Formula.Phi()),
                provenance,
                content),
            _ => throw new ArgumentOutOfRangeException(nameof(kind)),
        };
    }

    private static void WithRepository(
        Action<string> assertion,
        string doi = "10.1007/BF01389053")
    {
        var root = Path.Combine(Path.GetTempPath(), "stratalint-report-" + Guid.NewGuid().ToString("N"));
        var formalPath = Path.Combine(root, "D5", "S1", "Phase", "Basic.lean");
        var notes = Path.Combine(root, "Library", "notes");
        Directory.CreateDirectory(Path.GetDirectoryName(formalPath)!);
        Directory.CreateDirectory(notes);
        Directory.CreateDirectory(Path.Combine(root, "Blueprint"));
        File.WriteAllText(Path.Combine(root, "global.json"), "{}\n", new UTF8Encoding(false, true));
        File.WriteAllText(
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
            Directory.Delete(root, recursive: true);
        }
    }

    private static void WriteNote(
        string root,
        string bibkey,
        string title,
        string doi)
    {
        var notes = Path.Combine(root, "Library", "notes");
        Directory.CreateDirectory(notes);
        File.WriteAllText(
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
