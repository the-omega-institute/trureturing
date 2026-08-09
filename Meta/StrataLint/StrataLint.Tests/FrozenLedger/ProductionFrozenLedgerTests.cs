using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ProductionValidatorRejectsWhenEitherLedgerIsMissing(bool removeBaselineLedger)
    {
        var fixture = CreateFrozenValidatorFixture();
        var files = removeBaselineLedger ? fixture.BaselineFiles : fixture.CurrentFiles;
        foreach (var path in files.Keys
            .Where(FrozenLedgerChangeClassifier.IsAcceptedEventPath).ToArray())
        {
            files.Remove(path);
        }
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "frozen ledger shape is invalid");
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

}
