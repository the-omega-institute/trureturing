namespace StrataLint.Scribe.Tests;

public sealed class StatementProjectionPilotTests
{
    [Fact]
    public void DocumentDefinitionsLoadFromExplicitRepositoryRoot()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.LakefileInvalidOperation);
        var repositoryRoot = TemporaryFileSystem.Directory.CreateTempSubdirectory(
            "stratalint-scribe-explicit-root-");
        try
        {
            CopyPinnedProjectionFixtures(repository, repositoryRoot);
            var definitions = DocumentDefinitions.Discover(
                DocumentAssembly.Value,
                repositoryRoot.FullName);

            Assert.NotEmpty(definitions);
        }
        finally
        {
            repositoryRoot.Delete(recursive: true);
        }
    }

    [Fact]
    public void PinnedProjectionFixturesConstructEveryDocumentWithoutALiveReport()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.LakefileInvalidOperation);
        var repositoryRoot = TemporaryFileSystem.Directory.CreateTempSubdirectory(
            "stratalint-scribe-pinned-");
        try
        {
            CopyPinnedProjectionFixtures(repository, repositoryRoot);

            var definitions = DocumentDefinitions.Discover(
                DocumentAssembly.Value,
                repositoryRoot.FullName);

            Assert.Contains(definitions, static definition =>
                definition.Document.Header.Gid.Value == "D5/S3/Zeros/OffLineWitness");
        }
        finally
        {
            repositoryRoot.Delete(recursive: true);
        }
    }

    private static void CopyPinnedProjectionFixtures(
        RepositoryAccessor repository,
        DirectoryInfo repositoryRoot)
    {
        var projectionRoot = TemporaryFileSystem.Directory.CreateDirectory(
            Path.Combine(repositoryRoot.FullName, "Golden", "Projection"));
        repository.CopyTo(
            RepositoryRelativePath.Create("Golden/Projection/statement-projection-expansion-v1.json"),
            Path.Combine(projectionRoot.FullName, "statement-projection-expansion-v1.json"));
        repository.CopyTo(
            RepositoryRelativePath.Create("Golden/Projection/statement-projection-pilot-v1.json"),
            Path.Combine(projectionRoot.FullName, "statement-projection-pilot-v1.json"));
    }

    [Fact]
    public void DocumentDefinitionsFailClosedWithFixturePathForExplicitRepository()
    {
        var repositoryRoot = TemporaryFileSystem.Directory.CreateTempSubdirectory("stratalint-scribe-missing-");
        try
        {
            var exception = Assert.Throws<FileNotFoundException>(() =>
                DocumentDefinitions.Discover(
                    DocumentAssembly.Value,
                    repositoryRoot.FullName));

            Assert.Contains(repositoryRoot.FullName, exception.Message, StringComparison.Ordinal);
            Assert.Contains(
                "statement-projection-pilot-v1.json",
                exception.Message,
                StringComparison.Ordinal);
        }
        finally
        {
            repositoryRoot.Delete(recursive: true);
        }
    }

    [Fact]
    public void ProjectionsCheckReturnsZeroForMatchingPinnedFixtures()
    {
        using var repository = TemporaryRepository.WithReport(
            type: "statement-v1(uparams=[],type=es(l0))");
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(DocumentAssembly.Value,
            ["projections", "--check", "--report", "live-report.json"],
            repository.Path,
            output,
            error,
            repository.Report());

        Assert.Equal(0, exit);
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void ProjectionsCheckPrintsEveryPinnedFixtureMismatchAndReturnsOne()
    {
        using var repository = TemporaryRepository.WithReport(
            type: "statement-v1(uparams=[],type=es(l1))");
        repository.AddPinnedDeclaration(
            "D5.Test.missing",
            "statement-v1(uparams=[],type=es(l2))");
        var error = new StringWriter();

        var exit = ScribeCli.Run(DocumentAssembly.Value,
            ["projections", "--check", "--report", "live-report.json"],
            repository.Path,
            TextWriter.Null,
            error,
            repository.Report());

        Assert.Equal(1, exit);
        Assert.Equal(
            [
                "pinned statement projection differs from live report: D5.Test.declaration",
                "pinned statement projection is missing from live report: D5.Test.missing",
            ],
            error.ToString().Split(Environment.NewLine, StringSplitOptions.RemoveEmptyEntries));
    }

    [Theory]
    [InlineData("projections")]
    [InlineData("projections", "--check")]
    [InlineData("projections", "--report", "live-report.json")]
    [InlineData("projections", "--check", "--report")]
    [InlineData("projections", "--check", "--report", "live-report.json", "extra")]
    public void ProjectionsCheckRejectsOpenArgumentShapesWithExitTwo(params string[] arguments)
    {
        var error = new StringWriter();

        var exit = ScribeCli.Run(DocumentAssembly.Value,
            arguments,
            TemporaryFileSystem.Directory.GetCurrentDirectory(),
            TextWriter.Null,
            error);

        Assert.Equal(2, exit);
        Assert.Contains(
            "projections --check --report <file>",
            error.ToString(),
            StringComparison.Ordinal);
    }
}
