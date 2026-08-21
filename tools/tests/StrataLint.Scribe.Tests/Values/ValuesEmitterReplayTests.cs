using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class ValuesEmitterReplayTests
{
    [Fact]
    public void R15ValuesCheckIgnoresTrackedProjectionFreshnessAndProducerStillEmits()
    {
        var temporary = TemporaryFileSystem.Directory.CreateTempSubdirectory(
            "stratalint-r15-values-replay-");
        try
        {
            foreach (var relativePath in CanonicalValuesWriter.InputPaths)
            {
                var destination = Path.Combine(temporary.FullName, relativePath);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                TemporaryFileSystem.File.WriteAllText(
                    destination,
                    relativePath == ValuesKernelDataLoader.RelativePath
                        ? SyntheticCatalog
                        : "synthetic producer input\n",
                    new UTF8Encoding(false, true));
            }

            var projection = Path.Combine(temporary.FullName, CanonicalValuesWriter.RelativePath);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(projection)!);
            TemporaryFileSystem.File.WriteAllText(projection, "stale\n", new UTF8Encoding(false, true));
            var output = new StringWriter();
            var error = new StringWriter();

            var checkExit = ValuesEmitter.Emit(
                temporary.FullName,
                check: true,
                output,
                error);

            Assert.Equal(0, checkExit);
            Assert.Contains(
                "verified: values producer is byte deterministic",
                output.ToString(),
                StringComparison.Ordinal);
            Assert.Empty(error.ToString());
            Assert.Equal("stale\n", TemporaryFileSystem.File.ReadAllText(projection));

            var emitExit = ValuesEmitter.Emit(
                temporary.FullName,
                check: false,
                TextWriter.Null,
                error);

            Assert.Equal(0, emitExit);
            Assert.Empty(error.ToString());
            Assert.Equal(
                CanonicalValuesWriter.Write(temporary.FullName).ToArray(),
                TemporaryFileSystem.File.ReadAllBytes(projection));
        }
        finally
        {
            temporary.Delete(recursive: true);
        }
    }

    private const string SyntheticCatalog = """
        schema_version = 1

        [[constants]]
        id = "D5/Synthetic"
        lean_gid = "D5/S3/Constants/Values.synthetic"
        lean_statement_sha256 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        status = "registered-open"
        definition = "synthetic registered value"
        method = "registered-open"
        reference_value = "0"
        reference_error = "0"
        open_reason = "synthetic input is intentionally not computed"
        refs = {}
        computation = "none"
        """ + "\n";
}
