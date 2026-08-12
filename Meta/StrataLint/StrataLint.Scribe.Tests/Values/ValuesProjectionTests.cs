using System.Text.Json;
using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class ValuesProjectionTests
{
    [Fact]
    public void ExactQuadraticEvaluationUsesAControlledDecimalInterval()
    {
        var definition = ValuesKernelDataLoader.LoadRepository(RepositoryAccessor.Discover(RepositoryRootCriterion.ValuesProducerDirectoryNotFound).Root.FullPath)
            .Single(static item => item.Id == "D5/kappa");

        var result = ValuesEvaluator.Evaluate(definition);

        Assert.Equal("1/(2*phi)", result.Value);
        Assert.Equal("0.309016994374947424", result.Decimal);
        Assert.Equal("0", result.Error);
        var receipt = Assert.Single(result.KernelReceipts);
        Assert.Equal("exact-quadratic", receipt.Kernel);
        Assert.Equal("24", receipt.Parameters["decimal_digits"]);
        Assert.Equal(PhiFractionalPartKernel.PrecisionStrategy, receipt.Parameters["precision_strategy"]);
    }

    [Fact]
    public void CphiProjectionRequiresFourWindowsForItsSpreadEstimate()
    {
        var definition = ValuesKernelDataLoader.LoadRepository(RepositoryAccessor.Discover(RepositoryRootCriterion.ValuesProducerDirectoryNotFound).Root.FullPath)
            .Single(static item => item.Id == "D5/Cphi") with
        {
            Computation = new ValueComputation.Cphi(new CphiKernelSpec(
                TermCount: 12,
                FractionalPartDecimalDigits: 30,
                FirstFibonacciIndex: 5,
                LastFibonacciIndex: 5)),
        };

        var exception = Assert.Throws<InvalidOperationException>(() => ValuesEvaluator.Evaluate(definition));

        Assert.Contains("at least four", exception.Message, StringComparison.Ordinal);
    }

}
