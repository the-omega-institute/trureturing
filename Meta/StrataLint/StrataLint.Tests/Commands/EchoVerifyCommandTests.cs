using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class EchoVerifyCommandTests
{
    private const string Summary = "# Echo Residual Summary\n\n- unresolved_subitems: 1\n";

    [Fact]
    public void ContentAddressedBlockRendersTheResidualProjection()
    {
        var rendered = EchoResidualBlock.Render(Summary);

        Assert.StartsWith(
            "<!-- echo-residual-summary:v3 residual=sha256:05f4f3c3989efd7578fb7fdf6716b7a76aed13b8e840bd5a3fd624b86dd9bca9 -->\n",
            rendered,
            StringComparison.Ordinal);
        Assert.Equal(Summary, rendered[(rendered.IndexOf('\n') + 1)..]);
    }
}
