using System.Text;
using System.Security.Cryptography;

namespace StrataLint.Scribe.Tests;

public sealed class EmissionTests
{
    [Fact]
    public void RepositoryValidationFailsBeforeWritingDanglingDocuments()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-validation-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        try
        {
            var error = new StringWriter();
            var report = LeanReportFixture.ForDocuments(
                DocumentDefinitions.All.Select(static definition => definition.Document));

            var exit = ScribeEmitter.Emit(
                root,
                check: false,
                TextWriter.Null,
                error,
                report,
                validateRepository: true);

            Assert.Equal(1, exit);
            Assert.Contains("dangling-gid", error.ToString(), StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(
                root,
                DocumentDefinitions.All[0].RelativePath.Value)));
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void MalformedLibraryMetadataIsAStableEmissionFailure()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-library-" + Guid.NewGuid().ToString("N"));
        var notes = Path.Combine(root, "Library", "notes");
        Directory.CreateDirectory(notes);
        try
        {
            File.WriteAllText(
                Path.Combine(notes, "sos1957threegap.md"),
                "---\nbibkey: sos1957threegap\nauthors: Vera T. Sos\nyear: 1957\n"
                + "title: Invalid\ndoi: not-a-doi\n"
                + "claim: Invalid fixture.\nstrata_touched: []\nlicense: citation-only\n"
                + "triage: anchor\n---\n");
            var error = new StringWriter();
            var report = LeanReportFixture.ForDocuments(
                DocumentDefinitions.All.Select(static definition => definition.Document));

            var exit = ScribeEmitter.Emit(
                root,
                check: false,
                TextWriter.Null,
                error,
                report,
                validateRepository: true);

            Assert.Equal(1, exit);
            Assert.Contains("describe red code=invalid-doi", error.ToString(), StringComparison.Ordinal);
            Assert.Contains("malformed DOI", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

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
            CopyRepositoryLibrary(root);

            var emitExit = ScribeEmitter.Emit(root, check: false, output, error, report);

            Assert.Equal(0, emitExit);
            Assert.Empty(error.ToString());
            Assert.True(File.Exists(Path.Combine(
                root,
                ScribeEmitter.AttestationRelativePath)));
            var firstEmission = new Dictionary<string, byte[]>(StringComparer.Ordinal);
            var citations = LibraryNoteCatalog.Load(root).Citations;
            foreach (var definition in DocumentDefinitions.All)
            {
                var path = Path.Combine(root, definition.RelativePath.Value);
                firstEmission.Add(definition.RelativePath.Value, File.ReadAllBytes(path));
                Assert.Equal(
                    CanonicalMarkdownWriter.Write(
                        definition.Document,
                        report,
                        citations).ToArray(),
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
            var repositoryRoot = FindRepositoryRoot();
            foreach (var source in Directory.EnumerateFiles(
                         Path.Combine(repositoryRoot, "D5"),
                         "*.lean",
                         SearchOption.AllDirectories))
            {
                var relative = Path.GetRelativePath(repositoryRoot, source);
                var destination = Path.Combine(root, relative);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                File.Copy(source, destination);
            }
            CopyRepositoryLibrary(root);

            Assert.Equal(0, ScribeEmitter.Emit(
                root,
                check: false,
                TextWriter.Null,
                TextWriter.Null,
                report));
            var initialVerification = ScribeEmitter.Verify(root, TextWriter.Null, report);
            Assert.NotNull(initialVerification);
            Assert.True(initialVerification.ReferencesDeclaration(
                "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"));
            Assert.True(initialVerification.ReferencesDeclaration(
                "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec"));

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
        Assert.Contains("emit|catalog|emit-values|filemap [--check]", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void EveryBlueprintMarkdownHasExactlyOneDiscoveredScribeDefinition()
    {
        var root = FindRepositoryRoot();
        var markdownPaths = Directory
            .EnumerateFiles(Path.Combine(root, "Blueprint"), "*.md", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
            .Order(StringComparer.Ordinal)
            .ToArray();
        var definitionPaths = DocumentDefinitions.All
            .Select(static definition => definition.RelativePath.Value)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(markdownPaths, definitionPaths);
        Assert.All(markdownPaths, path => Assert.True(
            File.Exists(Path.Combine(root, path[..^".md".Length] + ".scribe.cs")),
            $"missing Scribe definition for {path}"));
    }

    private static string Sha256(byte[] bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static void CopyRepositoryLibrary(string destinationRoot)
    {
        var repositoryRoot = FindRepositoryRoot();
        foreach (var source in Directory.EnumerateFiles(
                     Path.Combine(repositoryRoot, "Library"),
                     "*.md",
                     SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(repositoryRoot, source);
            var destination = Path.Combine(destinationRoot, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(source, destination);
        }
    }

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
