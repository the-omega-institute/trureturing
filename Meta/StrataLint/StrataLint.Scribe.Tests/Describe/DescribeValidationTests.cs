using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeValidationTests
{
    private const string FormalPath = "D5/S1/Phase/Basic.lean";

    [Fact]
    public void ValidatorRejectsDanglingInlineAndLiteratureReferences()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(
                GidRef.Create("D5/S1/Phase/Missing"),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/sos1957threegap")));

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            Assert.Contains(findings, finding => finding.Code == "dangling-gid");
            Assert.Contains(findings, finding => finding.Code == "dangling-literature-reference");
        });
    }

    [Fact]
    public void ValidatorRejectsDanglingGidInsideLibraryMetadata()
    {
        WithRepository(root =>
        {
            WriteNote(root, "D5/S1/Phase/Missing");
            var document = CreateDocument(
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/sos1957threegap")));

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            var finding = Assert.Single(findings);
            Assert.Equal("dangling-library-gid", finding.Code);
            Assert.Equal("Library/notes/sos1957threegap.md", finding.Path);
        });
    }

    [Fact]
    public void ValidatorAcceptsResolvableRepositoryAndLibraryReferences()
    {
        WithRepository(root =>
        {
            var formalPath = Path.Combine(root, "D5", "S1", "Phase", "Basic.lean");
            Directory.CreateDirectory(Path.GetDirectoryName(formalPath)!);
            File.WriteAllText(formalPath, "namespace D5.S1.Phase\n", new UTF8Encoding(false, true));
            WriteNote(root, "D5/S1/Phase/Basic");
            var document = CreateDocument(
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/sos1957threegap")));

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            Assert.Empty(findings);
        });
    }

    [Fact]
    public void ValidatorRejectsLiteratureReferenceToTheWrongSplitBucket()
    {
        WithRepository(root =>
        {
            WriteNote(root, "D5/S1/Phase/Basic", bucket: "Zeros");
            var document = CreateDocument(
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/Weil/sos1957threegap")));

            var finding = Assert.Single(DescribeRepositoryValidator.Validate(root, [document]));

            Assert.Equal("dangling-literature-reference", finding.Code);
            Assert.Contains("D5/L/Weil/sos1957threegap", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorAcceptsLiteratureHeaderAnchorFromASplitBucket()
    {
        WithRepository(root =>
        {
            WriteNote(root, "D5/S1/Phase/Basic", bucket: "Zeros");
            var header = DefinitionDsl.Header(
                "D5/S1/Phase/Basic",
                "Split-bucket anchor fixture.",
                Anchor.ParseCanonical("lit/sos1957threegap"));
            var document = CreateDocument(
                header,
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.RepoDerived());

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            Assert.Empty(findings);
        });
    }

    [Fact]
    public void ValidatorReportsDuplicateBibkeysAcrossBucketsWithoutThrowing()
    {
        WithRepository(root =>
        {
            WriteNote(root, "D5/S1/Phase/Basic");
            WriteNote(root, "D5/S1/Phase/Basic", bucket: "Zeros");
            var document = CreateDocument(
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.RepoDerived());

            var findings = DescribeRepositoryValidator.Validate(root, [document]);

            Assert.Contains(findings, finding => finding.Code == "duplicate-bibkey");
        });
    }

    [Fact]
    public void ValidatorRejectsMissingFormalDeclarationSelectorWhenLeanReportIsAvailable()
    {
        WithRepository(root =>
        {
            var document = CreateDocument(
                GidRef.Create("D5/S1/Phase/Basic.missing_declaration"),
                DescribeProvenance.RepoDerived());
            var report = LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
                {
                    [FormalPath] = new LeanFileReport([], []),
                });

            var findings = DescribeRepositoryValidator.Validate(root, [document], report);

            var finding = Assert.Single(findings);
            Assert.Equal("dangling-gid", finding.Code);
            Assert.Contains("missing_declaration", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsDanglingTaskTriageReference()
    {
        WithRepository(root =>
        {
            WriteNote(
                root,
                "D5/S1/Phase/Basic",
                triage: "task(D5/S1/Phase/Missing)");
            var document = CreateDocument(
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.RepoDerived());

            var finding = Assert.Single(DescribeRepositoryValidator.Validate(root, [document]));

            Assert.Equal("dangling-library-gid", finding.Code);
            Assert.Contains("D5/S1/Phase/Missing", finding.Message, StringComparison.Ordinal);
        });
    }

    [Fact]
    public void ValidatorRejectsDanglingDocumentAndEvidenceHeaderGids()
    {
        WithRepository(root =>
        {
            var missingDocument = CreateDocument(
                DefinitionDsl.Header("D5/S1/Phase/Missing", "Missing document fixture."),
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.RepoDerived());
            var evidenceHeader = DocumentHeader.Create(
                GidRef.Create("D5/S1/Phase/Basic"),
                Generality.Instance,
                GidRef.Create("D5/B/S1/Phase/Basic"),
                new EvidenceMirror.Artifact(GidRef.Create(
                    "D5/E/S1/Phase/Missing.result--json")),
                [],
                Digest.Create("Missing evidence fixture."));
            var missingEvidence = CreateDocument(
                evidenceHeader,
                GidRef.Create("D5/S1/Phase/Basic"),
                DescribeProvenance.RepoDerived());

            var findings = DescribeRepositoryValidator.Validate(
                root,
                [missingDocument, missingEvidence]);

            Assert.Contains(findings, finding =>
                finding.Code == "dangling-document-gid"
                && finding.Message.Contains("D5/S1/Phase/Missing", StringComparison.Ordinal));
            Assert.Contains(findings, finding =>
                finding.Code == "dangling-evidence-gid"
                && finding.Message.Contains(
                    "D5/E/S1/Phase/Missing.result--json",
                    StringComparison.Ordinal));
        });
    }

    private static ScribeDocument CreateDocument(
        GidRef inlineReference,
        DescribeProvenance provenance) => CreateDocument(
        DefinitionDsl.Header("D5/S1/Phase/Basic", "Validation fixture."),
        inlineReference,
        provenance);

    private static ScribeDocument CreateDocument(
        DocumentHeader header,
        GidRef inlineReference,
        DescribeProvenance provenance) => ScribeDocument.Create(
        header,
        Heading.Create("Validation"),
        BlockSequence.Create(
        [
            new DocumentBlock.Describe(
                DescribeId.Create("validated-claim"),
                DescribeKind.Remark,
                Heading.Create("Validated claim"),
                DescribeStatement.FromFormula(new Formula.Phi()),
                provenance,
                BlockSequence.Create(
                [
                    DefinitionDsl.Paragraph(new Inline.GidReference(inlineReference)),
                ])),
        ]));

    private static void WriteNote(
        string root,
        string touchedGid,
        string triage = "anchor",
        string bucket = "notes")
    {
        var directory = Path.Combine(root, "Library", bucket);
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, "sos1957threegap.md"),
            "---\n"
            + "bibkey: sos1957threegap\n"
            + "authors: Vera T. Sos\n"
            + "year: 1957\n"
            + "title: On the three gap theorem\n"
            + "doi: 10.1007/BF01389053\n"
            + "claim: Gap lengths for irrational rotations.\n"
            + "strata_touched:\n"
            + $"  - {touchedGid}\n"
            + "license: citation-only\n"
            + $"triage: {triage}\n"
            + "---\n",
            new UTF8Encoding(false, true));
    }

    private static void WithRepository(Action<string> assertion)
    {
        var root = Path.Combine(Path.GetTempPath(), "stratalint-describe-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        try
        {
            var formalPath = Path.Combine(root, "D5", "S1", "Phase", "Basic.lean");
            Directory.CreateDirectory(Path.GetDirectoryName(formalPath)!);
            File.WriteAllText(formalPath, "namespace D5.S1.Phase\n", new UTF8Encoding(false, true));
            assertion(root);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }
}
