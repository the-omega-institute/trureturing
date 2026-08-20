using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Tests;

public sealed class LatexWriterBoundaryTests
{
    [Fact]
    public void RejectsRowBreakFollowedByOpenBracket()
    {
        var formula = F.Seq(
            F.RowBreak,
            F.OpenBracket,
            F.Operatorname,
            F.Grp(F.Id("MetricSpace")));

        var exception = Assert.Throws<InvalidOperationException>(
            () => LatexWriter.Write(formula, "D5/S0/Naming/Conservation/CompletionEmbeddingResidual"));

        Assert.Contains(
            "D5/S0/Naming/Conservation/CompletionEmbeddingResidual",
            exception.Message,
            StringComparison.Ordinal);
        Assert.Contains("byte offset 2", exception.Message, StringComparison.Ordinal);
        Assert.Contains("\\\\[", exception.Message, StringComparison.Ordinal);
        Assert.Contains("insert FormulaDsl.Grp()", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsAlignedRowStartingWithOpenBracket()
    {
        Formula formula = new Formula.Aligned(
        [
            F.Id("x"),
            F.Seq(F.OpenBracket, F.Id("condition"), F.CloseBracket),
        ]);

        var exception = Assert.Throws<InvalidOperationException>(
            () => LatexWriter.Write(formula, "direct aligned construction"));

        Assert.Contains("direct aligned construction", exception.Message, StringComparison.Ordinal);
        Assert.Contains("byte offset", exception.Message, StringComparison.Ordinal);
        Assert.Contains("\\\\[", exception.Message, StringComparison.Ordinal);
        Assert.Contains("insert FormulaDsl.Grp()", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RejectsThroughWriteStatementAndWriteUtf8()
    {
        var formula = F.Seq(F.RowBreak, F.OpenBracket);

        var statementException = Assert.Throws<InvalidOperationException>(
            () => LatexWriter.WriteStatement(formula));
        var utf8Exception = Assert.Throws<InvalidOperationException>(
            () => LatexWriter.WriteUtf8(formula));

        Assert.Contains("standalone formula", statementException.Message, StringComparison.Ordinal);
        Assert.Contains("standalone formula", utf8Exception.Message, StringComparison.Ordinal);
        Assert.Contains("insert FormulaDsl.Grp()", statementException.Message, StringComparison.Ordinal);
        Assert.Contains("insert FormulaDsl.Grp()", utf8Exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AcceptsExplicitEmptyGroupAfterRowBreak()
    {
        var formula = F.Seq(F.RowBreak, F.Grp(), F.OpenBracket);

        Assert.Equal("\\\\{}[", LatexWriter.Write(formula));
    }

}
