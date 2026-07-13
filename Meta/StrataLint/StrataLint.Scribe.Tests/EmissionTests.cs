using System.Text;
using System.Security.Cryptography;

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
            var report = LeanReportFixture.ForDocuments(
                DocumentDefinitions.All.Select(static definition => definition.Document));
            foreach (var definition in DocumentDefinitions.All)
            {
                var relativeSource = definition.RelativePath.Value[..^3] + ".scribe.cs";
                var destination = Path.Combine(root, relativeSource);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                // Deterministic CI builds map [CallerFilePath] to the /_/ source root,
                // so fixture copies must resolve through the runtime repository root.
                File.Copy(Path.Combine(FindRepositoryRoot(), relativeSource), destination);
            }

            var emitExit = ScribeEmitter.Emit(root, check: false, output, error, report);

            Assert.Equal(0, emitExit);
            Assert.Empty(error.ToString());
            Assert.True(File.Exists(Path.Combine(
                root,
                ScribeEmitter.AttestationRelativePath)));
            var firstEmission = new Dictionary<string, byte[]>(StringComparer.Ordinal);
            foreach (var definition in DocumentDefinitions.All)
            {
                var path = Path.Combine(root, definition.RelativePath.Value);
                firstEmission.Add(definition.RelativePath.Value, File.ReadAllBytes(path));
                Assert.Equal(
                    CanonicalMarkdownWriter.Write(definition.Document, report).ToArray(),
                    File.ReadAllBytes(path));
            }

            output.GetStringBuilder().Clear();
            var secondEmitExit = ScribeEmitter.Emit(root, check: false, output, error, report);

            Assert.Equal(0, secondEmitExit);
            Assert.Contains("emitted: 0 changed blueprint(s)", output.ToString(), StringComparison.Ordinal);
            foreach (var definition in DocumentDefinitions.All)
            {
                Assert.Equal(
                    firstEmission[definition.RelativePath.Value],
                    File.ReadAllBytes(Path.Combine(root, definition.RelativePath.Value)));
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
                error,
                report);
            Assert.Equal(0, cliCheckExit);

            var driftedPath = Path.Combine(root, DocumentDefinitions.All[0].RelativePath.Value);
            File.WriteAllText(driftedPath, "drift\n", new UTF8Encoding(false, true));

            var checkExit = ScribeEmitter.Emit(root, check: true, output, error, report);

            Assert.Equal(1, checkExit);
            Assert.Equal("drift\n", File.ReadAllText(driftedPath));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);

            File.WriteAllBytes(
                driftedPath,
                firstEmission[DocumentDefinitions.All[0].RelativePath.Value]);
            var attestationPath = Path.Combine(root, ScribeEmitter.AttestationRelativePath);
            File.WriteAllText(attestationPath, "drift\n", new UTF8Encoding(false, true));
            error.GetStringBuilder().Clear();

            var attestationCheckExit = ScribeEmitter.Emit(
                root,
                check: true,
                TextWriter.Null,
                error,
                report);

            Assert.Equal(1, attestationCheckExit);
            Assert.Contains(ScribeEmitter.AttestationRelativePath, error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void InvalidLeanReportFailsBeforeAnyBlueprintIsWritten()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);

        try
        {
            var firstPath = Path.Combine(root, DocumentDefinitions.All[0].RelativePath.Value);
            Directory.CreateDirectory(Path.GetDirectoryName(firstPath)!);
            File.WriteAllText(firstPath, "sentinel\n", new UTF8Encoding(false, true));
            var error = new StringWriter();

            var exit = ScribeEmitter.Emit(
                root,
                check: false,
                TextWriter.Null,
                error,
                StrataLint.Engine.LeanAxiomReport.Create(
                    new Dictionary<string, StrataLint.Engine.LeanFileReport>()));

            Assert.Equal(1, exit);
            Assert.Contains("emit failed", error.ToString(), StringComparison.Ordinal);
            Assert.Equal("sentinel\n", File.ReadAllText(firstPath));
            Assert.False(File.Exists(
                Path.Combine(root, DocumentDefinitions.All[^1].RelativePath.Value)));
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void VerificationRejectsJointlyForgedEmissionAndAttestation()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);

        try
        {
            var report = LeanReportFixture.ForDocuments(
                DocumentDefinitions.All.Select(static definition => definition.Document));
            foreach (var definition in DocumentDefinitions.All)
            {
                var relativeSource = definition.RelativePath.Value[..^3] + ".scribe.cs";
                var destination = Path.Combine(root, relativeSource);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                // Deterministic CI builds map [CallerFilePath] to the /_/ source root,
                // so fixture copies must resolve through the runtime repository root.
                File.Copy(Path.Combine(FindRepositoryRoot(), relativeSource), destination);
            }

            Assert.Equal(0, ScribeEmitter.Emit(
                root,
                check: false,
                TextWriter.Null,
                TextWriter.Null,
                report));
            Assert.NotNull(ScribeEmitter.Verify(root, TextWriter.Null, report));

            var emissionPath = Path.Combine(root, DocumentDefinitions.All[0].RelativePath.Value);
            var originalEmission = File.ReadAllBytes(emissionPath);
            var forgedEmission = Encoding.UTF8.GetBytes("# forged emission\n");
            File.WriteAllBytes(emissionPath, forgedEmission);
            var attestationPath = Path.Combine(root, ScribeEmitter.AttestationRelativePath);
            var attestation = File.ReadAllText(attestationPath, Encoding.UTF8)
                .Replace(Sha256(originalEmission), Sha256(forgedEmission), StringComparison.Ordinal);
            File.WriteAllText(attestationPath, attestation, new UTF8Encoding(false));
            var error = new StringWriter();

            var verification = ScribeEmitter.Verify(root, error, report);

            Assert.Null(verification);
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void CliRejectsAnythingOutsideClosedCommandsAndOptionalCheck()
    {
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            ["emit", "--write-somewhere"],
            Directory.GetCurrentDirectory(),
            TextWriter.Null,
            error);

        Assert.Equal(2, exit);
        Assert.Contains("emit|catalog|emit-values [--check]", error.ToString(), StringComparison.Ordinal);
    }

    private static string Sha256(byte[] bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new InvalidOperationException("repository root was not found above the test base directory");
    }
}
