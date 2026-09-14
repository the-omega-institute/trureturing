namespace StrataLint.Scribe.Tests;

public sealed partial class ProblemCandidateTests
{
    [Theory]
    [InlineData("null", "http://example.org/source")]
    [InlineData("null", "/source")]
    [InlineData("10.1000/sample", "http://example.org/source")]
    public void LoaderRejectsInvalidUrlSources(string doi, string url) => WithCatalog(
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["sample-open-problem.md"] = DoiAndUrlCandidate(doi, url),
        },
        root => Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root)));

    [Fact]
    public void LoaderKeepsBothDoiAndUrlSources() => WithCatalog(
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["sample-open-problem.md"] = DoiAndUrlCandidate(
                "10.1000/sample", "https://example.org/source"),
        },
        root =>
        {
            var candidate = Assert.Single(ProblemCandidateCatalog.Load(root).Candidates);
            Assert.Equal("10.1000/sample", candidate.Doi!.Value);
            Assert.Equal("https://example.org/source", candidate.Url!.AbsoluteUri);
        });

    [Theory]
    [InlineData("10.1000/sample", "https://example.org/source")]
    [InlineData("10.1000/sample", null)]
    [InlineData("null", "https://example.org/source")]
    public void ValidatorAcceptsCandidateSourcesCarriedByANoteWithDoiAndUrl(string doi, string? url) =>
        WithRepository(
            url is null ? DoiCandidate(doi) : DoiAndUrlCandidate(doi, url),
            DoiAndUrlNote("10.1000/sample", "https://example.org/source"),
            ["D5/S1/Phase/Basic"],
            root => Assert.Empty(DescribeRepositoryValidator.Validate(root, [])),
            ["D5/S1/Phase/Basic"]);

    [Theory]
    [InlineData("10.1000/sample", "https://example.org/different")]
    [InlineData("10.1000/different", "https://example.org/source")]
    public void ValidatorRejectsCandidateWhoseSecondSourceDisagreesWithTheNote(string doi, string url) =>
        WithRepository(
            DoiAndUrlCandidate(doi, url),
            DoiAndUrlNote("10.1000/sample", "https://example.org/source"),
            ["D5/S1/Phase/Basic"],
            root => Assert.Equal("problem-source-mismatch",
                Assert.Single(DescribeRepositoryValidator.Validate(root, [])).Code),
            ["D5/S1/Phase/Basic"]);

    [Fact]
    public void ValidatorRejectsCandidateUrlThatTheNoteDoesNotCarry() => WithRepository(
        DoiAndUrlCandidate("10.1000/sample", "https://example.org/source"),
        Note("sos1957threegap", "10.1000/sample"),
        ["D5/S1/Phase/Basic"],
        root => Assert.Equal("problem-source-mismatch",
            Assert.Single(DescribeRepositoryValidator.Validate(root, [])).Code),
        ["D5/S1/Phase/Basic"]);

    [Fact]
    public void ValidatorAcceptsMatchingStableUrlsWithoutDois() => WithRepository(
        DoiCandidate("null").Replace("doi: null\n",
            "doi: null\nurl: https://example.org/source\n", StringComparison.Ordinal),
        Note("sos1957threegap", "null").Replace("doi: null\n",
            "doi: null\nurl: https://example.org/source\n", StringComparison.Ordinal),
        ["D5/S1/Phase/Basic"],
        root => Assert.Empty(DescribeRepositoryValidator.Validate(root, [])),
        ["D5/S1/Phase/Basic"]);

    [Fact]
    public void ValidatorRejectsMismatchedStableUrls() => WithRepository(
        DoiCandidate("null").Replace("doi: null\n",
            "doi: null\nurl: https://example.org/source\n", StringComparison.Ordinal),
        Note("sos1957threegap", "null").Replace("doi: null\n",
            "doi: null\nurl: https://example.org/different\n", StringComparison.Ordinal),
        ["D5/S1/Phase/Basic"],
        root => Assert.Equal("problem-source-mismatch",
            Assert.Single(DescribeRepositoryValidator.Validate(root, [])).Code),
        ["D5/S1/Phase/Basic"]);

    [Theory]
    [InlineData("null")]
    [InlineData("2305.08349")]
    [InlineData("arXiv:2305.08349")]
    [InlineData("2305.08349v1")]
    [InlineData("2305.083491")]
    [InlineData("")]
    [InlineData("https://doi.org/10.1006/eujc.1998.0211")]
    [InlineData("10.1006/")]
    [InlineData("10.1006/with space")]
    public void CatalogRejectsMalformedDoi(string doi) => WithCatalog(
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["sample-open-problem.md"] = DoiCandidate(doi),
        },
        root =>
        {
            var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
            Assert.Contains("doi", error.Message, StringComparison.OrdinalIgnoreCase);
        });

    [Fact]
    public void CatalogRejectsBothSourceKeys() => WithCatalog(
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["sample-open-problem.md"] = Candidate("sample-open-problem")
                .Replace("triage: theorem", "arxiv_id: 2305.08349\ntriage: theorem",
                    StringComparison.Ordinal),
        },
        root =>
        {
            var error = Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root));
            Assert.Contains("missing or unknown metadata fields", error.Message, StringComparison.Ordinal);
        });

    [Theory]
    [InlineData("arxiv_id: 2305.08349")]
    [InlineData("doi: 10.48550/arXiv.2305.08349\narxiv_id: 2305.08349")]
    public void ValidatorRejectsArxivIdMetadata(string source) => WithRepository(
        Candidate("sample-open-problem")
            .Replace("doi: 10.48550/arXiv.2305.08349", source, StringComparison.Ordinal),
        Note("sos1957threegap", "10.48550/arXiv.2305.08349"),
        ["D5/S1/Phase/Basic"],
        root =>
        {
            var finding = Assert.Single(DescribeRepositoryValidator.Validate(root, []));
            Assert.Equal("invalid-problem-candidate", finding.Code);
            Assert.Equal("Problems/sample-open-problem.md", finding.Path);
            Assert.Contains("missing or unknown metadata fields", finding.Message, StringComparison.Ordinal);
        },
        ["D5/S1/Phase/Basic"]);

    [Fact]
    public void CatalogRejectsUnknownFieldInDoiForm() => WithCatalog(
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["sample-open-problem.md"] = DoiCandidate("10.1006/eujc.1998.0211")
                .Replace("triage: theorem", "status: resolved\ntriage: theorem", StringComparison.Ordinal),
        },
        root => Assert.Throws<FormatException>(() => ProblemCandidateCatalog.Load(root)));

    [Theory]
    [InlineData("10.1006/eujc.1998.0211")]
    [InlineData("10.4153/CMB-1986-050-0")]
    [InlineData("10.48550/arXiv.2305.08349")]
    [InlineData("10.46298/dmtcs.17199")]
    public void CatalogAcceptsCompleteDoiWithoutArxivId(string doi) => WithCatalog(
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["sample-open-problem.md"] = DoiCandidate(doi),
        },
        root =>
        {
            var candidate = Assert.Single(ProblemCandidateCatalog.Load(root).Candidates);
            Assert.Equal("sample-open-problem", candidate.Slug);
            Assert.Equal(doi, candidate.Doi!.Value);
        });

    [Theory]
    [InlineData("10.1006/eujc.1998.0211")]
    [InlineData("10.48550/arXiv.2305.08349")]
    [InlineData("10.46298/dmtcs.17199")]
    public void ValidatorAcceptsExactDoiBinding(string doi) => WithDoiRepository(
        doi, doi, root =>
        {
            Assert.Equal(doi, Assert.Single(ProblemCandidateCatalog.Load(root).Candidates).Doi!.Value);
            Assert.Empty(DescribeRepositoryValidator.Validate(root, []));
        });

    [Theory]
    [InlineData("10.4153/CMB-1986-050-0", "10.4153/cmb-1986-050-0")]
    [InlineData("10.48550/arXiv.2305.08349", "10.48550/arxiv.2305.08349")]
    public void ValidatorRejectsDoiBindingThatDiffersOnlyInCase(string doi, string noteDoi) => WithDoiRepository(
        doi, noteDoi,
        root => Assert.Equal("problem-source-mismatch",
            Assert.Single(DescribeRepositoryValidator.Validate(root, [])).Code));

    [Fact]
    public void ValidatorRejectsDoiBindingToDifferentWork() => WithDoiRepository(
        "10.1006/eujc.1998.0211", "10.1216/rmj-2013-43-5-1707",
        root => Assert.Equal("problem-source-mismatch",
            Assert.Single(DescribeRepositoryValidator.Validate(root, [])).Code));

    [Fact]
    public void ValidatorRejectsDoiBindingToNoteWithoutDoi() => WithDoiRepository(
        "10.1006/eujc.1998.0211", "null",
        root => Assert.Equal("problem-source-mismatch",
            Assert.Single(DescribeRepositoryValidator.Validate(root, [])).Code));

    [Fact]
    public void ValidatorRejectsDoiBindingToMalformedNoteDoi() => WithDoiRepository(
        "10.1006/eujc.1998.0211", "not-a-doi",
        root =>
        {
            var findings = DescribeRepositoryValidator.Validate(root, []);
            Assert.Contains(findings, finding => finding.Code == "invalid-doi");
            Assert.Contains(findings, finding => finding.Code == "dangling-problem-bibkey");
        });

    [Fact]
    public void ValidatorRejectsDoiBindingWithoutExternalNote() => WithRepository(
        DoiCandidate("10.1006/eujc.1998.0211"),
        Note("slater1967gaps", "10.1006/eujc.1998.0211"),
        ["D5/S1/Phase/Basic"],
        root => Assert.Equal("dangling-problem-bibkey",
            Assert.Single(DescribeRepositoryValidator.Validate(root, [])).Code),
        ["D5/S1/Phase/Basic"]);

    private static string DoiCandidate(string doi) => Candidate("sample-open-problem", doi: doi);

    private static string DoiAndUrlCandidate(string doi, string url) => DoiCandidate(doi)
        .Replace($"doi: {doi}\n", $"doi: {doi}\nurl: {url}\n", StringComparison.Ordinal);

    private static string DoiAndUrlNote(string doi, string url) => Note("sos1957threegap", doi)
        .Replace($"doi: {doi}\n", $"doi: {doi}\nurl: {url}\n", StringComparison.Ordinal);

    private static void WithDoiRepository(string doi, string noteDoi, Action<string> assertion) =>
        WithRepository(DoiCandidate(doi), Note("sos1957threegap", noteDoi),
            ["D5/S1/Phase/Basic"], assertion, ["D5/S1/Phase/Basic"]);
}
