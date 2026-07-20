namespace StrataLint.Scribe.Tests;

public sealed class LatexStatementTests
{
    [Theory]
    [InlineData("$\\operatorname{Re}(s) = \\frac{1}{2}$")]
    [InlineData("$$\\begin{aligned}x &= 1 \\\\ y &= 2\\end{aligned}$$")]
    public void ValidStatementsPreserveTheirCanonicalDelimitersAndBytes(string value)
    {
        var statement = LatexStatement.Create(value);

        Assert.Equal(value, statement.Value);
        Assert.Equal(value, statement.ToString());
    }

    [Theory]
    [InlineData("")]
    [InlineData("   ")]
    [InlineData("x = 1")]
    [InlineData("$x = 1")]
    [InlineData("$ $")]
    [InlineData("$x { y$")]
    [InlineData("$x } y$")]
    [InlineData("$\\begin{aligned}x = 1\\end{cases}$")]
    [InlineData("$\\begin{foo-bar}x = 1\\end{foo-bar}$")]
    [InlineData("$\\begin aligned$")]
    [InlineData("$\\unknownmacro{x}$")]
    [InlineData("$x$ trailing")]
    [InlineData("$x\r\n= 1$")]
    public void InvalidStatementsAreRejected(string value)
    {
        Assert.Throws<ArgumentException>(() => LatexStatement.Create(value));
    }

    [Fact]
    public void NullStatementIsRejected()
    {
        Assert.Throws<ArgumentNullException>(() => LatexStatement.Create(null!));
    }
}
