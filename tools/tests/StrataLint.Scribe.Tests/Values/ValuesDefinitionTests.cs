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
    public void SyntheticCatalogPreservesStatusAndComputationContracts()
    {
        var directory = TemporaryFileSystem.Directory.CreateTempSubdirectory("stratalint-values-catalog-contract-");
        try
        {
            var path = Path.Combine(directory.FullName, "values-kernels.toml");
            TemporaryFileSystem.File.WriteAllText(path, SyntheticCatalog);
            var definitions = ValuesKernelDataLoader.LoadFile(path);

            Assert.Equal(2, definitions.Length);
            Assert.Equal(
                definitions.Length,
                definitions.Select(static definition => definition.Id)
                    .Distinct(StringComparer.Ordinal)
                    .Count());
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
        finally
        {
            directory.Delete(recursive: true);
        }
    }

    private const string SyntheticCatalog = """
        schema_version = 1

        [[constants]]
        id = "D5/Ah"
        lean_gid = "D5/S3/Constants/Values.ah"
        lean_statement_sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        status = "emitted"
        definition = "synthetic exact value"
        method = "exact-quadratic"
        reference_value = "1"
        reference_error = "0"
        error = "0"
        refs = {}
        computation = "exact-quadratic"
        rational_numerator = 1
        rational_denominator = 1
        sqrt_five_numerator = 0
        sqrt_five_denominator = 1

        [[constants]]
        id = "D5/Bh"
        lean_gid = "D5/S3/Constants/Values.bh"
        lean_statement_sha256 = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
        status = "registered-open"
        definition = "synthetic open value"
        method = "registered-open"
        reference_value = "0"
        reference_error = "0"
        open_reason = "synthetic input is intentionally not computed"
        refs = {}
        computation = "none"
        """ + "\n";
}
