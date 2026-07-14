namespace StrataLint.Scribe.Tests;

public sealed class ValuesDefinitionTests
{
    [Fact]
    public void CatalogDefinesAllFourteenConstantsAndKeepsUntranslatedInputsOpen()
    {
        var definitions = ValuesKernelDataLoader.LoadRepository(FindRepositoryRoot());

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
        var definition = ValuesKernelDataLoader.LoadRepository(FindRepositoryRoot())
            .Single(static item => item.Id == "D5/Cphi");
        var computation = Assert.IsType<ValueComputation.Cphi>(definition.Computation);

        var result = CphiKernel.Compute(computation.Spec);

        Assert.Equal(16, result.WindowMeans.Length);
        Assert.Equal(result.TermCount + 1L, result.WindowMeans[^1].EndExclusive);
        Assert.Equal(0.04576252043707622, result.Value, precision: 14);
        Assert.True(Math.Abs(result.Value - 0.045759332) > 1.1e-8);
        Assert.Equal(3_524_577, result.TermCount);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, ValuesKernelDataLoader.RelativePath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate the repository root.");
    }
}
