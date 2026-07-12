using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class EmissionTests
{
    [Fact]
    public void EmitWritesCanonicalFilesAndCheckDetectsDriftWithoutOverwriting()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);

        try
        {
            var output = new StringWriter();
            var error = new StringWriter();

            var emitExit = ScribeEmitter.Emit(root, check: false, output, error);

            Assert.Equal(0, emitExit);
            Assert.Empty(error.ToString());
            foreach (var definition in DocumentDefinitions.All)
            {
                var path = Path.Combine(root, definition.RelativePath.Value);
                Assert.Equal(
                    CanonicalMarkdownWriter.Write(definition.Document).ToArray(),
                    File.ReadAllBytes(path));
            }

            File.WriteAllText(
                Path.Combine(root, "global.json"),
                "{}\n",
                new UTF8Encoding(false, true));
            var nestedDirectory = Path.Combine(root, "Meta", "StrataLint");
            Directory.CreateDirectory(nestedDirectory);
            var cliCheckExit = ScribeCli.Run(
                ["emit", "--check"],
                nestedDirectory,
                output,
                error);
            Assert.Equal(0, cliCheckExit);

            var driftedPath = Path.Combine(root, DocumentDefinitions.All[0].RelativePath.Value);
            File.WriteAllText(driftedPath, "drift\n", new UTF8Encoding(false, true));

            var checkExit = ScribeEmitter.Emit(root, check: true, output, error);

            Assert.Equal(1, checkExit);
            Assert.Equal("drift\n", File.ReadAllText(driftedPath));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void CliRejectsAnythingOutsideEmitAndOptionalCheck()
    {
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            ["emit", "--write-somewhere"],
            Directory.GetCurrentDirectory(),
            TextWriter.Null,
            error);

        Assert.Equal(2, exit);
        Assert.Contains("emit [--check]", error.ToString(), StringComparison.Ordinal);
    }
}
