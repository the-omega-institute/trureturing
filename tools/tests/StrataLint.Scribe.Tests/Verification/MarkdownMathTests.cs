namespace StrataLint.Scribe.Tests;

public sealed class MarkdownMathTests
{
    [Fact]
    public void ReadsInlineAndDisplayFormulasAndLeavesCodeAlone()
    {
        const string markdown = """
            # Title

            Prose with $x + 1$ inline and a `$not math$` code span.

            $$\forall n, u_{n} = 1.$$

            ```lean
            theorem probe : $fake$ := by simp
            ```

            ~~~text
            $also not math$
            ~~~

            $$
            \sum_{n=0}^{\infty} n
            $$
            """;

        var formulas = MarkdownMath.Extract(markdown);

        Assert.Equal(
            [
                (false, "x + 1"),
                (true, @"\forall n, u_{n} = 1."),
                (true, "\n\\sum_{n=0}^{\\infty} n\n"),
            ],
            formulas.Select(static formula => (formula.Display, formula.Tex)));
    }

    [Fact]
    public void ReportsTheLineAFormulaOpensOn()
    {
        const string markdown = "# Title\n\nprose\n\n$$x$$\n\nmore $y$ prose\n";

        var formulas = MarkdownMath.Extract(markdown);

        Assert.Equal([(5, true), (7, false)], formulas.Select(static f => (f.Line, f.Display)));
    }

    [Fact]
    public void FencedLinesKeepTheirPlaceSoLaterLineNumbersHold()
    {
        const string markdown = "```text\n$fenced$\n```\n\n$$x$$\n";

        var formulas = MarkdownMath.Extract(markdown);

        Assert.Equal([(5, true, "x")], formulas.Select(static f => (f.Line, f.Display, f.Tex)));
    }

    [Fact]
    public void AnEscapedDollarIsProseAndAnUnpairedOneOpensNothing()
    {
        const string markdown = "cost \\$5 and \\$6, then $x$, and a lone $ here\n";

        var formulas = MarkdownMath.Extract(markdown);

        Assert.Equal([(false, "x")], formulas.Select(static formula => (formula.Display, formula.Tex)));
    }

    [Fact]
    public void AnInlineFormulaNeverCrossesALineButADisplayOneMay()
    {
        Assert.Empty(MarkdownMath.Extract("$open\nclose$\n"));
        Assert.Equal(
            [(true, "open\nclose")],
            MarkdownMath.Extract("$$open\nclose$$\n")
                .Select(static formula => (formula.Display, formula.Tex)));
    }
}
