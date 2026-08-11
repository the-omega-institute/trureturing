namespace StrataLint.Scribe.Tests;

public sealed class ValuesDefinitionTests
{
    [Fact]
    public void RepositoryCatalogUsesTheTopLevelGoldenDataHome()
    {
        Assert.Equal("Golden/values-kernels.toml", ValuesKernelDataLoader.RelativePath);
    }

    [Fact]
    public void CatalogSizeIsDefinedByTomlRows()
    {
        var directory = TemporaryFileSystem.Directory.CreateTempSubdirectory("stratalint-values-catalog-");
        try
        {
            var path = Path.Combine(directory.FullName, "values-kernels.toml");
            TemporaryFileSystem.File.WriteAllText(path, """
                schema_version = 1

                [[constants]]
                id = "D5/Bh"
                lean_gid = "D5/S3/Constants/Values.bh"
                lean_statement_sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                status = "registered-open"
                definition = "synthetic registered value"
                method = "registered-open"
                reference_value = "0"
                reference_error = "0"
                open_reason = "synthetic input is intentionally not computed"
                refs = {}
                computation = "none"
                """ + "\n");

            var definition = Assert.Single(ValuesKernelDataLoader.LoadFile(path));

            Assert.Equal("D5/Bh", definition.Id);
        }
        finally
        {
            directory.Delete(recursive: true);
        }
    }

    [Fact]
    public void CatalogDefinesAllFourteenConstantsAndKeepsUntranslatedInputsOpen()
    {
        var definitions = ValuesKernelDataLoader.LoadRepository(RepositoryAccessor.Discover().Root.FullPath);

        Assert.Equal(14, definitions.Length);
        Assert.Equal(
            definitions.Length,
            definitions.Select(static definition => definition.Id)
                .Distinct(StringComparer.Ordinal)
                .Count());
        Assert.Equal(
            [
                "D5/Bh",
                "D5/T0",
                "D5/T1",
                "D5/c1",
                "D5/c2",
                "D5/delta.mean",
            ],
            definitions.Where(static definition => definition.Status is ValueDefinitionStatus.RegisteredOpen)
                .Select(static definition => definition.Id)
                .Order(StringComparer.Ordinal));
        Assert.All(
            definitions.Where(static definition => definition.Status is ValueDefinitionStatus.Emitted),
            static definition => Assert.NotNull(definition.Computation));
        Assert.All(
            definitions.Where(static definition => definition.Status is ValueDefinitionStatus.RegisteredOpen),
            static definition =>
            {
                Assert.Null(definition.Computation);
                Assert.False(string.IsNullOrWhiteSpace(definition.OpenReason));
            });
    }

    [Fact]
    public void CanonicalCphiSpecRecordsTheReferenceMismatchWithoutTuning()
    {
        var definition = ValuesKernelDataLoader.LoadRepository(RepositoryAccessor.Discover().Root.FullPath)
            .Single(static item => item.Id == "D5/Cphi");
        var computation = Assert.IsType<ValueComputation.Cphi>(definition.Computation);

        var result = CphiKernel.Compute(computation.Spec);

        Assert.Equal(16, result.WindowMeans.Length);
        Assert.Equal(result.TermCount + 1L, result.WindowMeans[^1].EndExclusive);
        Assert.Equal(0.04576252043707622, result.Value, precision: 14);
        Assert.True(Math.Abs(result.Value - 0.045759332) > 1.1e-8);
        Assert.Equal(3_524_577, result.TermCount);
    }
}
