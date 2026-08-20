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
            var repository = RepositoryAccessor.Discover(
                RepositoryRootCriterion.ValuesProducerDirectoryNotFound);
            foreach (var relativePath in CanonicalValuesWriter.InputPaths)
            {
                var destination = Path.Combine(temporary.FullName, relativePath);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                repository.CopyTo(RepositoryRelativePath.Create(relativePath), destination);
            }

            var projection = Path.Combine(temporary.FullName, CanonicalValuesWriter.RelativePath);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(projection)!);
            TemporaryFileSystem.File.WriteAllText(projection, "stale\n", new UTF8Encoding(false, true));
            var error = new StringWriter();

            var checkExit = ValuesEmitter.Emit(
                temporary.FullName,
                check: true,
                TextWriter.Null,
                error);

            Assert.Equal(0, checkExit);
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
}
