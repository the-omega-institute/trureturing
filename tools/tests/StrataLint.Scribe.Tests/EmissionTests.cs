using System.Text;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class EmissionTests
{

    [Fact]
    public void EmitWritesCanonicalFilesAndCheckIgnoresReaderSnapshotFreshness()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);

        try
        {
            var definition = SyntheticDefinition();
            DocumentDefinition[] definitions = [definition];
            WriteSyntheticScribeInputs(root, definition);
            var output = new StringWriter();
            var error = new StringWriter();
            var report = LeanReportFixture.ForDocuments([definition.Document]);

            var emitExit = ScribeEmitter.Emit(
                root, check: false, output, error, report, definitions);

            Assert.Equal(0, emitExit);
            Assert.Empty(error.ToString());
            Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(
                root,
                ScribeEmitter.AttestationRelativePath)));
            var emissionPath = Path.Combine(root, definition.RelativePath.Value);
            var firstEmission = TemporaryFileSystem.File.ReadAllBytes(emissionPath);
            var citations = LibraryNoteCatalog.Load(root).Citations;
            ScribeDocument[] documents = [definition.Document];
            var graph = DocumentGraphAssembler.Assemble(
                documents,
                DeclarationCatalog.Create(report));
            Assert.Equal(
                CanonicalMarkdownWriter.Write(
                    definition.Document,
                    DeclarationCatalog.Create(report),
                    citations,
                    graph).ToArray(),
                firstEmission);

            output.GetStringBuilder().Clear();
            var secondEmitExit = ScribeEmitter.Emit(
                root, check: false, output, error, report, definitions);

            Assert.Equal(0, secondEmitExit);
            Assert.Contains("emitted: 0 changed blueprint(s)", output.ToString(), StringComparison.Ordinal);
            Assert.Equal(firstEmission, TemporaryFileSystem.File.ReadAllBytes(emissionPath));

            output.GetStringBuilder().Clear();
            TemporaryFileSystem.File.WriteAllText(emissionPath, "drift\n", new UTF8Encoding(false, true));

            var checkExit = ScribeEmitter.Emit(
                root, check: true, output, error, report, definitions);

            Assert.Equal(0, checkExit);
            Assert.Contains("verified: 1 current blueprint render(s)", output.ToString(), StringComparison.Ordinal);
            Assert.Equal("drift\n", TemporaryFileSystem.File.ReadAllText(emissionPath));
            Assert.Empty(error.ToString());

            TemporaryFileSystem.File.WriteAllBytes(emissionPath, firstEmission);
            var attestationPath = Path.Combine(root, ScribeEmitter.AttestationRelativePath);
            TemporaryFileSystem.File.Delete(attestationPath);
            error.GetStringBuilder().Clear();

            var cleanCheckoutExit = ScribeEmitter.Emit(
                root,
                check: true,
                TextWriter.Null,
                error,
                report,
                definitions);

            Assert.Equal(0, cleanCheckoutExit);
            Assert.Empty(error.ToString());

            TemporaryFileSystem.File.WriteAllText(attestationPath, "drift\n", new UTF8Encoding(false, true));
            error.GetStringBuilder().Clear();

            var attestationCheckExit = ScribeEmitter.Emit(
                root,
                check: true,
                TextWriter.Null,
                error,
                report,
                definitions);

            Assert.Equal(0, attestationCheckExit);
            Assert.Empty(error.ToString());
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void CliRejectsAnythingOutsideClosedCommandsAndOptionalCheck()
    {
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            DocumentlessAssembly.Value,
            ["emit", "--write-somewhere"],
            TemporaryFileSystem.Directory.GetCurrentDirectory(),
            TextWriter.Null,
            error);

        Assert.Equal(2, exit);
        Assert.Contains("emit|emit-values|filemap [--check]", error.ToString(), StringComparison.Ordinal);
    }

    private static DocumentDefinition SyntheticDefinition()
    {
        var document = ScribeDocument.Create(
            DefinitionDsl.Header(
                "D5/S0/Synthetic/CheckMode",
                "Synthetic check-mode fixture."),
            DefinitionDsl.H("Synthetic check mode"),
            DefinitionDsl.Blocks(
                DefinitionDsl.Paragraph(DefinitionDsl.Text("Synthetic body."))));
        return DocumentDefinition.Create(
            document,
            "Blueprint/D5/S0/Synthetic/CheckMode.scribe.cs");
    }

    private static void WriteSyntheticScribeInputs(
        string root,
        DocumentDefinition definition) =>
        SyntheticScribeRepository.WriteInputs(root, definition);

}
