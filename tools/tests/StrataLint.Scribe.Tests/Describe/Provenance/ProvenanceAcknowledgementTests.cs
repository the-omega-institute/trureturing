using System.Text;
using System.Text.Json;

namespace StrataLint.Scribe.Tests;

public sealed class ProvenanceAcknowledgementTests
{
    private const string DocumentGid = "D5/S1/Phase/Basic";
    private const string NoteGid = "D5/L/Quantum/sample1987paper";

    [Fact]
    public void RepositoryValidatorRejectsMissingAcknowledgementNote()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(AssessedProvenance.FromRepo(Note()));

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            Assert.Contains(findings, static finding =>
                finding.Code == "dangling-literature-reference"
                && finding.Message.Contains(NoteGid, StringComparison.Ordinal));
        });
    }

    [Fact]
    public void RepositoryValidatorRejectsMalformedDoiOnAcknowledgement()
    {
        WithRepository(root =>
        {
            WriteNote(root, bucket: "Quantum", doi: "not-a-doi");
            var document = CreateDocument(AssessedProvenance.FromRepo(Note()));

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            Assert.Contains(findings, static finding => finding.Code == "invalid-doi");
            Assert.Contains(findings, static finding =>
                finding.Code == "dangling-literature-reference"
                && finding.Message.Contains(NoteGid, StringComparison.Ordinal));
        });
    }

    [Fact]
    public void RepositoryValidatorRejectsAcknowledgementReferenceToWrongSplitBucket()
    {
        WithRepository(root =>
        {
            WriteNote(root, bucket: "notes");
            var document = CreateDocument(AssessedProvenance.FromRepo(Note()));

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            Assert.Contains(findings, static finding =>
                finding.Code == "dangling-literature-reference"
                && finding.Message.Contains(NoteGid, StringComparison.Ordinal));
        });
    }

    [Fact]
    public void ContentGovernanceRequiresVerifiedLocatorForAcknowledgement()
    {
        WithRepository(root =>
        {
            WriteNote(root, bucket: "Quantum", includeLocator: false);
            var document = CreateDocument(AssessedProvenance.FromRepo(Note()));
            var inspection = LibraryNoteCatalog.Inspect(root);

            var findings = DescribeContentGovernance.ValidateReferencedNoteLocators(
                root,
                [document],
                inspection);

            Assert.Contains(findings, static finding =>
                finding.Code == "incomplete-library-locator"
                && finding.Path == "Library/Quantum/sample1987paper.md");
        });
    }

    [Fact]
    public void ReportSeparatesAcknowledgementsFromAttestingLiterature()
    {
        WithRepository(root =>
        {
            WriteNote(root, bucket: "Quantum");
            var note = Note();
            var searchReceipt = GidRef.Create(DocumentGid);
            var document = ScribeDocument.Create(
                DefinitionDsl.Header(DocumentGid, "Report acknowledgement fixture."),
                Heading.Create("Report acknowledgements"),
                BlockSequence.Create(
                [
                    CreateDescribe("repository", "Repository", AssessedProvenance.FromRepo(note)),
                    CreateDescribe("literature", "Literature", AssessedProvenance.FromLiterature(note)),
                    CreateDescribe(
                        "candidate",
                        "Candidate",
                        AssessedProvenance.NovelAfterSearch(searchReceipt, note)),
                ]));

            using var json = JsonDocument.Parse(
                DescribeReportWriter.WriteJson(DescribeReport.Build(root, [document])));
            var nodes = json.RootElement.GetProperty("nodes").EnumerateArray().ToArray();
            var repository = Assert.Single(nodes, static node =>
                node.GetProperty("title").GetString() == "Repository");
            var literature = Assert.Single(nodes, static node =>
                node.GetProperty("title").GetString() == "Literature");
            var candidate = Assert.Single(nodes, static node =>
                node.GetProperty("title").GetString() == "Candidate");

            Assert.Equal("repo-derived", repository.GetProperty("provenance").GetString());
            Assert.Equal(JsonValueKind.Null, repository.GetProperty("literature_gid").ValueKind);
            Assert.Equal(
                [NoteGid],
                repository.GetProperty("acknowledgement_gids").EnumerateArray()
                    .Select(static item => item.GetString()));
            Assert.Equal("literature-attested", literature.GetProperty("provenance").GetString());
            Assert.Equal(NoteGid, literature.GetProperty("literature_gid").GetString());
            Assert.Empty(literature.GetProperty("acknowledgement_gids").EnumerateArray());
            Assert.Equal("suspected-novel", candidate.GetProperty("provenance").GetString());
            Assert.Equal(
                [NoteGid],
                candidate.GetProperty("acknowledgement_gids").EnumerateArray()
                    .Select(static item => item.GetString()));
        });
    }

    [Fact]
    public void MarkdownDistinguishesAcknowledgementFromAttestation()
    {
        var note = Note();
        var document = ScribeDocument.Create(
            DefinitionDsl.Header(DocumentGid, "Rendered acknowledgement fixture."),
            Heading.Create("Rendered acknowledgements"),
            BlockSequence.Create(
            [
                CreateDescribe("repository", "Repository", AssessedProvenance.FromRepo(note)),
                CreateDescribe("literature", "Literature", AssessedProvenance.FromLiterature(note)),
            ]));

        var text = Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(document, citations: Citations()).AsSpan());

        Assert.Contains("*Source.* Repository-derived.", text, StringComparison.Ordinal);
        Assert.Contains(
            "*Acknowledgement.* Sample Author (1987). *A sample paper*. "
            + "DOI: [10.1000/sample.1987](https://doi.org/10.1000/sample.1987).",
            text,
            StringComparison.Ordinal);
        Assert.Contains(
            "*Citation.* Sample Author (1987). *A sample paper*. "
            + "DOI: [10.1000/sample.1987](https://doi.org/10.1000/sample.1987).",
            text,
            StringComparison.Ordinal);
    }

    [Fact]
    public void QuestPdfChangesWhenTypedAcknowledgementIsAdded()
    {
        var withoutAcknowledgement = CreateDocument(AssessedProvenance.FromRepo());
        var withAcknowledgement = CreateDocument(AssessedProvenance.FromRepo(Note()));

        var plainPdf = QuestPdfWriter.Write(withoutAcknowledgement, citations: Citations());
        var acknowledgedPdf = QuestPdfWriter.Write(withAcknowledgement, citations: Citations());

        Assert.NotEqual(plainPdf.Length, acknowledgedPdf.Length);
    }

    private static LibraryNoteRef Note() => LibraryNoteRef.Create(NoteGid);

    private static IReadOnlyDictionary<string, LiteratureCitation> Citations() =>
        new Dictionary<string, LiteratureCitation>(StringComparer.Ordinal)
        {
            ["sample1987paper"] = LiteratureCitation.Create(
                "Sample Author",
                1987,
                "A sample paper",
                "10.1000/sample.1987"),
        };

    private static ScribeDocument CreateDocument(AssessedProvenance provenance) =>
        ScribeDocument.Create(
            DefinitionDsl.Header(DocumentGid, "Acknowledgement fixture."),
            Heading.Create("Acknowledgement"),
            BlockSequence.Create(
            [
                CreateDescribe("claim", "Claim", provenance),
            ]));

    private static DocumentBlock.Describe CreateDescribe(
        string id,
        string title,
        AssessedProvenance provenance) =>
        Describe.Remark(
            DescribeId.Create(id),
            Heading.Create(title),
            new Formula.Phi(),
            provenance,
            DefinitionDsl.Blocks(
                DefinitionDsl.Paragraph(DefinitionDsl.Text("Typed narrative."))));

    private static IEnumerable<DocumentBlock> EnumerateBlocks(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (nested is null) continue;
            foreach (var descendant in EnumerateBlocks(nested)) yield return descendant;
        }
    }

    private static void WriteNote(
        string root,
        string bucket,
        string doi = "10.1000/sample.1987",
        bool includeLocator = true)
    {
        var directory = Path.Combine(root, "Library", bucket);
        TemporaryFileSystem.Directory.CreateDirectory(directory);
        var locator = includeLocator
            ? $"\n## Verified locator\n\n- DOI: https://doi.org/{doi}\n"
            : string.Empty;
        TemporaryFileSystem.File.WriteAllText(
            Path.Combine(directory, "sample1987paper.md"),
            "---\n"
            + "bibkey: sample1987paper\n"
            + "authors: Sample Author\n"
            + "year: 1987\n"
            + "title: A sample paper\n"
            + $"doi: {doi}\n"
            + "claim: A sample claim.\n"
            + "strata_touched:\n"
            + $"  - {DocumentGid}\n"
            + "license: citation-only\n"
            + "triage: anchor\n"
            + "---\n"
            + locator,
            new UTF8Encoding(false, true));
    }

    private static void WithRepository(Action<string> assertion)
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-provenance-ack-" + Guid.NewGuid().ToString("N"));
        var formalPath = Path.Combine(root, "D5", "S1", "Phase", "Basic.lean");
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(formalPath)!);
        TemporaryFileSystem.File.WriteAllText(
            formalPath,
            "namespace D5.S1.Phase\n",
            new UTF8Encoding(false, true));
        try
        {
            assertion(root);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }
}
