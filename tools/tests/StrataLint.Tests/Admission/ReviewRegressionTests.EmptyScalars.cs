using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReviewRegressionTests
{
    [Theory]
    [InlineData("json", "")]
    [InlineData("json", " \t\n")]
    [InlineData("json", "\uFEFF")]
    [InlineData("json", " \uFEFF \n")]
    [InlineData("yaml", "")]
    [InlineData("yaml", " \t\n")]
    [InlineData("yaml", "\uFEFF")]
    [InlineData("yaml", " \uFEFF \n")]
    public void Sl019AcceptsEmptyNormalizedScalarsAndStillScansSiblingRecords(string format, string value)
    {
        var fixture = new RuleFixture();
        var path = $"Evidence/D5/S0/Carrier/Empty.run.{format}";
        var scalar = JsonSerializer.Serialize(value);
        fixture.Files[path] = format == "json" ? $"{{\"a\":{scalar}}}\n" : $"a: {scalar}\n";

        var empty = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), ActualDelta(fixture));
        Assert.Empty(empty.Diagnostics);

        fixture.Files[path] = format == "json"
            ? $"{{\"a\":{scalar},\"b\":{{\"kind\":\"tension\",\"state\":\"unresolved\"}}}}\n"
            : $"a: {scalar}\nb:\n  kind: tension\n  state: unresolved\n";
        var anomaly = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(19), ActualDelta(fixture));
        Assert.Contains(anomaly.Diagnostics, diagnostic => diagnostic.Path == path
            && diagnostic.Message.Contains("unledgered anomaly", StringComparison.Ordinal));
    }
}
