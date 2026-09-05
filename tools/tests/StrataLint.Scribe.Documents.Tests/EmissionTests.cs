using System.Text;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class EmissionTests
{
    [Fact]
    public void RepositoryValidationFailsBeforeWritingDanglingDocuments()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-validation-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        CopyProjectionFixtures(root);
        try
        {
            var error = new StringWriter();
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));

            var exit = ScribeEmitter.Emit(DocumentAssembly.Value,
                root,
                check: false,
                TextWriter.Null,
                error,
                report,
                validateRepository: true);

            Assert.Equal(1, exit);
            Assert.Contains("dangling-gid", error.ToString(), StringComparison.Ordinal);
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(
                root,
                DocumentAssembly.Definitions[0].RelativePath.Value)));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void MalformedLibraryMetadataIsAStableEmissionFailure()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-library-" + Guid.NewGuid().ToString("N"));
        var notes = Path.Combine(root, "Library", "notes");
        TemporaryFileSystem.Directory.CreateDirectory(notes);
        CopyProjectionFixtures(root);
        try
        {
            TemporaryFileSystem.File.WriteAllText(
                Path.Combine(notes, "sos1957threegap.md"),
                "---\nbibkey: sos1957threegap\nauthors: Vera T. Sos\nyear: 1957\n"
                + "title: Invalid\ndoi: not-a-doi\n"
                + "claim: Invalid fixture.\nstrata_touched: []\nlicense: citation-only\n"
                + "triage: anchor\n---\n");
            var error = new StringWriter();
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));

            var exit = ScribeEmitter.Emit(DocumentAssembly.Value,
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
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void InvalidLeanReportFailsBeforeAnyBlueprintIsWritten()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        CopyProjectionFixtures(root);

        try
        {
            var firstPath = Path.Combine(root, DocumentAssembly.Definitions[0].RelativePath.Value);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(firstPath)!);
            TemporaryFileSystem.File.WriteAllText(firstPath, "sentinel\n", new UTF8Encoding(false, true));
            var error = new StringWriter();

            var exit = ScribeEmitter.Emit(
                DocumentAssembly.Value,
                root,
                check: false,
                TextWriter.Null,
                error,
                StrataLint.Engine.LeanAxiomReport.Create(
                    new Dictionary<string, StrataLint.Engine.LeanFileReport>()));

            Assert.Equal(1, exit);
            Assert.Contains("emit failed", error.ToString(), StringComparison.Ordinal);
            Assert.Equal("sentinel\n", TemporaryFileSystem.File.ReadAllText(firstPath));
            Assert.False(TemporaryFileSystem.File.Exists(
                Path.Combine(root, DocumentAssembly.Definitions[^1].RelativePath.Value)));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void VerificationUsesCurrentRenderInsteadOfJointlyForgedSnapshot()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        CopyProjectionFixtures(root);

        try
        {
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));
            foreach (var definition in DocumentAssembly.Definitions)
            {
                var relativeSource = definition.RelativePath.Value[..^3] + ".scribe.cs";
                var destination = Path.Combine(root, relativeSource);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                // Deterministic CI builds map [CallerFilePath] to the /_/ source root,
                // so fixture copies must resolve through the runtime repository root.
                RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation).CopyTo(
                    RepositoryRelativePath.Create(relativeSource), destination);
            }
            var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation);
            foreach (var source in repository.EnumerateFiles(
                         RepositoryRelativePath.Create("D5"), "*.lean"))
            {
                var destination = Path.Combine(root, source.Value);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                repository.CopyTo(source, destination);
            }
            CopyRepositoryLibrary(root);

            Assert.Equal(0, ScribeEmitter.Emit(DocumentAssembly.Value,
                root,
                check: false,
                TextWriter.Null,
                TextWriter.Null,
                report));
            var initialVerification = ScribeEmitter.Verify(DocumentAssembly.Value, root, TextWriter.Null, report);
            Assert.NotNull(initialVerification);
            Assert.True(initialVerification.ReferencesDeclaration(
                "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"));
            Assert.True(initialVerification.ReferencesDeclaration(
                "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec"));

            var emissionPath = Path.Combine(root, DocumentAssembly.Definitions[0].RelativePath.Value);
            var originalEmission = TemporaryFileSystem.File.ReadAllBytes(emissionPath);
            var forgedEmission = Encoding.UTF8.GetBytes("# forged emission\n");
            TemporaryFileSystem.File.WriteAllBytes(emissionPath, forgedEmission);
            var attestationPath = Path.Combine(root, ScribeEmitter.AttestationRelativePath);
            var attestation = TemporaryFileSystem.File.ReadAllText(attestationPath, Encoding.UTF8)
                .Replace(Sha256(originalEmission), Sha256(forgedEmission), StringComparison.Ordinal);
            TemporaryFileSystem.File.WriteAllText(attestationPath, attestation, new UTF8Encoding(false));
            var error = new StringWriter();

            var verification = ScribeEmitter.Verify(DocumentAssembly.Value, root, error, report);

            Assert.NotNull(verification);
            Assert.True(verification!.TryGet(
                DocumentAssembly.Definitions[0].Document.Header.Gid.Value,
                out var verified));
            Assert.Equal(Sha256(originalEmission), verified.EmissionSha256);
            Assert.NotEqual(Sha256(forgedEmission), verified.EmissionSha256);
            Assert.Empty(error.ToString());
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void VerificationToleratesCandidateOnlyAttestationEntry()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        CopyProjectionFixtures(root);

        try
        {
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));
            PrepareEmittedRepository(root, report);

            var baseline = ScribeEmitter.Verify(DocumentAssembly.Value, root, TextWriter.Null, report);
            Assert.NotNull(baseline);

            // A candidate that adds a brand-new Blueprint scribe emits an attestation entry for a
            // document GID that is absent from the base binary's DocumentAssembly.Definitions. The base
            // binary cannot render that candidate-only document, so its recomputed attestation omits
            // the entry and byte-differs from the candidate on-disk attestation. Every base-owned
            // emission remains byte-identical, so the capability must still vouch for the base-owned
            // documents rather than collapse to null (which would un-absorb every base-owned atom).
            var attestationPath = Path.Combine(root, ScribeEmitter.AttestationRelativePath);
            var original = TemporaryFileSystem.File.ReadAllText(attestationPath, Encoding.UTF8);
            var injected = InjectCandidateOnlyAttestationEntry(original);
            Assert.NotEqual(original, injected);
            TemporaryFileSystem.File.WriteAllText(attestationPath, injected, new UTF8Encoding(false));

            var error = new StringWriter();
            var verification = ScribeEmitter.Verify(DocumentAssembly.Value, root, error, report);

            Assert.NotNull(verification);
            Assert.True(verification!.ReferencesDeclaration(
                "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"));
            Assert.True(verification.ReferencesDeclaration(
                "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec"));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void VerificationSkipsBinaryOnlyDocumentAbsentFromTree()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        CopyProjectionFixtures(root);

        try
        {
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));
            var victim = DocumentAssembly.Definitions.Single(static definition =>
                definition.Document.Header.Gid.Value == "D5/S1/Scale/CarrierFoundations");
            var retained = DocumentAssembly.Definitions.Where(static definition =>
                definition.Document.Header.Gid.Value is "D5/S0/Carrier/GoldenRatio"
                    or "D5/S1/Scale/FibonacciEigen").ToArray();
            var definitions = IncludeDocumentDependencyClosure(report, [victim, .. retained]);
            PrepareEmittedRepository(root, report, definitions);

            // The candidate harness compiles a newer document set than the baseline tree it
            // replays during conservative verification. A compiled document whose .scribe.cs
            // source is absent from the evaluated tree belongs to a world that tree has not
            // adopted: the verifier must skip it and still vouch for every document the tree
            // does own. Collapsing to null would un-absorb every base-owned atom of the older
            // tree — the exact mirror of the candidate-only tolerance above. Deleting a
            // base-owned source cannot launder a forgery through this skip: receipts that
            // reference the absent document gap out downstream and the deletion itself is a
            // protected-surface change.
            var victimSourcePath = Path.Combine(root, victim.RelativePath.Value[..^3] + ".scribe.cs");
            var victimEmissionPath = Path.Combine(root, victim.RelativePath.Value);
            var victimEntry =
                "{\"definition_path\": \"Blueprint/D5/S1/Scale/CarrierFoundations.scribe.cs\", "
                + "\"definition_sha256\": \"" + Sha256(TemporaryFileSystem.File.ReadAllBytes(victimSourcePath)) + "\", "
                + "\"emission_path\": \"Blueprint/D5/S1/Scale/CarrierFoundations.md\", "
                + "\"emission_sha256\": \"" + Sha256(TemporaryFileSystem.File.ReadAllBytes(victimEmissionPath)) + "\", "
                + "\"gid\": \"D5/S1/Scale/CarrierFoundations\"}";
            TemporaryFileSystem.File.Delete(victimSourcePath);
            TemporaryFileSystem.File.Delete(victimEmissionPath);
            var attestationPath = Path.Combine(root, ScribeEmitter.AttestationRelativePath);
            var original = TemporaryFileSystem.File.ReadAllText(attestationPath, Encoding.UTF8);
            var pruned = original.Replace(victimEntry + ", ", string.Empty, StringComparison.Ordinal);
            Assert.NotEqual(original, pruned);
            TemporaryFileSystem.File.WriteAllText(attestationPath, pruned, new UTF8Encoding(false));

            var error = new StringWriter();
            var verification = ScribeEmitter.Verify(DocumentAssembly.Value, root, error, report);

            Assert.NotNull(verification);
            Assert.Equal(string.Empty, error.ToString());
            Assert.True(verification!.ReferencesDeclaration(
                "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"));
            Assert.False(verification.ReferencesDeclaration(
                "D5/S1/Scale/CarrierFoundations.golden_carrier_foundations"));
            Assert.False(verification.TryGet("D5/S1/Scale/CarrierFoundations", out _));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void VerificationUsesCurrentRenderWhenSnapshotForgeryIncludesCandidateOnlyEntry()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        CopyProjectionFixtures(root);

        try
        {
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));
            var target = DocumentAssembly.Definitions[0];
            var definitions = IncludeDocumentDependencyClosure(report, [target]);
            PrepareEmittedRepository(root, report, definitions);

            // Forge both a reader snapshot and its run-local attestation, then splice in a candidate-only
            // entry. Verification must ignore both forged byte sources and issue the capability from the
            // canonical render produced by this run.
            var emissionPath = Path.Combine(root, DocumentAssembly.Definitions[0].RelativePath.Value);
            var originalEmission = TemporaryFileSystem.File.ReadAllBytes(emissionPath);
            var forgedEmission = Encoding.UTF8.GetBytes("# forged emission\n");
            TemporaryFileSystem.File.WriteAllBytes(emissionPath, forgedEmission);
            var attestationPath = Path.Combine(root, ScribeEmitter.AttestationRelativePath);
            var attestation = TemporaryFileSystem.File.ReadAllText(attestationPath, Encoding.UTF8)
                .Replace(Sha256(originalEmission), Sha256(forgedEmission), StringComparison.Ordinal);
            attestation = InjectCandidateOnlyAttestationEntry(attestation);
            TemporaryFileSystem.File.WriteAllText(attestationPath, attestation, new UTF8Encoding(false));

            var emitError = new StringWriter();
            var exit = ScribeEmitter.Emit(
                root,
                check: true,
                TextWriter.Null,
                emitError,
                report,
                definitions);
            var verifyError = new StringWriter();
            var verification = ScribeEmitter.Verify(DocumentAssembly.Value, root, verifyError, report);

            Assert.Equal(0, exit);
            Assert.NotNull(verification);
            Assert.True(verification!.TryGet(
                DocumentAssembly.Definitions[0].Document.Header.Gid.Value,
                out var verified));
            Assert.Equal(Sha256(originalEmission), verified.EmissionSha256);
            Assert.NotEqual(Sha256(forgedEmission), verified.EmissionSha256);
            Assert.Empty(emitError.ToString());
            Assert.Empty(verifyError.ToString());
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void VerificationToleratesDocumentAbsentFromEvaluatedTree()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);
        CopyProjectionFixtures(root);

        try
        {
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));
            PrepareEmittedRepository(root, report);

            // Mirror the conservative-extension baseline-tree replay: the candidate harness knows a
            // document (compiled into DocumentAssembly.Definitions) whose .scribe.cs source, .md emission, and
            // Lean declaration are all absent from the evaluated (older) tree — a not-yet-materialized
            // protected-surface addition. The base binary that already admitted this tree never saw the
            // document, so voiding the capability would make the candidate block what the baseline admits.
            var absent = DocumentAssembly.Definitions.Single(static definition =>
                definition.Document.Header.Gid.Value == "D5/S1/Scale/CarrierFoundations");
            Assert.NotEqual("D5/S0/Carrier/GoldenRatio", absent.Document.Header.Gid.Value);
            Assert.NotEqual("D5/S1/Scale/FibonacciEigen", absent.Document.Header.Gid.Value);
            TemporaryFileSystem.File.Delete(Path.Combine(root, absent.RelativePath.Value));
            TemporaryFileSystem.File.Delete(Path.Combine(root, absent.RelativePath.Value[..^3] + ".scribe.cs"));

            var reportWithoutAbsent = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions
                    .Where(definition => definition != absent)
                    .Select(static definition => definition.Document));

            var error = new StringWriter();
            var verification = ScribeEmitter.Verify(DocumentAssembly.Value, root, error, reportWithoutAbsent);

            Assert.NotNull(verification);
            Assert.True(verification!.ReferencesDeclaration(
                "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"));
            Assert.True(verification.ReferencesDeclaration(
                "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec"));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void VerificationProducesCurrentCapabilityWhenReaderSnapshotIsMissing()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);

        try
        {
            var report = LeanReportFixture.ForDocuments(
                DocumentAssembly.Definitions.Select(static definition => definition.Document));
            PrepareEmittedRepository(root, report);

            // A missing tracked .md is irrelevant to check mode: the producer has enough source
            // to render and verify the document without consulting the reader snapshot.
            var target = DocumentAssembly.Definitions[0];
            var targetPath = target.RelativePath.Value;
            var canonicalEmission = TemporaryFileSystem.File.ReadAllBytes(Path.Combine(root, targetPath));
            TemporaryFileSystem.File.Delete(Path.Combine(root, targetPath));

            var emitError = new StringWriter();
            var exit = ScribeEmitter.Emit(DocumentAssembly.Value,
                root,
                check: true,
                TextWriter.Null,
                emitError,
                report);
            var verifyError = new StringWriter();
            var verification = ScribeEmitter.Verify(DocumentAssembly.Value, root, verifyError, report);

            Assert.Equal(0, exit);
            Assert.NotNull(verification);
            Assert.True(verification!.TryGet(target.Document.Header.Gid.Value, out var verified));
            Assert.Equal(Sha256(canonicalEmission), verified.EmissionSha256);
            Assert.Empty(emitError.ToString());
            Assert.Empty(verifyError.ToString());
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

        var exit = ScribeCli.Run(DocumentAssembly.Value,
            ["emit", "--write-somewhere"],
            TemporaryFileSystem.Directory.GetCurrentDirectory(),
            TextWriter.Null,
            error);

        Assert.Equal(2, exit);
        Assert.Contains("emit|emit-values|filemap [--check]", error.ToString(), StringComparison.Ordinal);
    }

    private const string CandidateOnlyGid = "D5/S9/Candidate/PrimeFactorization";

    private static string Sha256(byte[] bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));

    private static void PrepareEmittedRepository(
        string root,
        LeanAxiomReport report,
        IReadOnlyList<DocumentDefinition>? definitions = null)
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation);
        CopyProjectionFixtures(root);
        if (definitions is null)
        {
            foreach (var definition in DocumentAssembly.Definitions)
            {
                var relativeSource = definition.RelativePath.Value[..^3] + ".scribe.cs";
                var destination = Path.Combine(root, relativeSource);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                // Deterministic CI builds map [CallerFilePath] to the /_/ source root,
                // so fixture copies must resolve through the runtime repository root.
                repository.CopyTo(RepositoryRelativePath.Create(relativeSource), destination);
            }
        }
        else
        {
            foreach (var definition in definitions)
            {
                SyntheticScribeRepository.WriteInputs(root, definition);
            }
        }

        foreach (var source in repository.EnumerateFiles(
                     RepositoryRelativePath.Create("D5"), "*.lean"))
        {
            var destination = Path.Combine(root, source.Value);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            repository.CopyTo(source, destination);
        }

        CopyRepositoryLibrary(root, includeBackfill: definitions is null);

        var error = new StringWriter();
        var exit = definitions is null
            ? ScribeEmitter.Emit(DocumentAssembly.Value, root, check: false, TextWriter.Null, error, report)
            : ScribeEmitter.Emit(root, check: false, TextWriter.Null, error, report, definitions);
        if (exit != 0)
        {
            throw new InvalidOperationException(
                $"fixture emission was not clean: {error.ToString().TrimEnd()}");
        }
    }

    private static string InjectCandidateOnlyAttestationEntry(string attestation)
    {
        var entry =
            "{\"definition_path\": \"Blueprint/" + CandidateOnlyGid + ".scribe.cs\", "
            + "\"definition_sha256\": \"sha256:" + new string('a', 64) + "\", "
            + "\"emission_path\": \"Blueprint/" + CandidateOnlyGid + ".md\", "
            + "\"emission_sha256\": \"sha256:" + new string('b', 64) + "\", "
            + "\"gid\": \"" + CandidateOnlyGid + "\"}, ";
        return attestation.Replace("\"entries\": [", "\"entries\": [" + entry, StringComparison.Ordinal);
    }

    private static IReadOnlyList<DocumentDefinition> IncludeDocumentDependencyClosure(
        LeanAxiomReport report,
        IReadOnlyList<DocumentDefinition> roots)
    {
        var byGid = DocumentAssembly.Definitions.ToDictionary(
            static definition => definition.Document.Header.Gid.Value,
            StringComparer.Ordinal);
        var graph = DocumentGraphAssembler.Assemble(
            byGid.Values.Select(static definition => definition.Document),
            DeclarationCatalog.Create(report));
        var selected = roots.ToDictionary(
            static definition => definition.Document.Header.Gid.Value,
            StringComparer.Ordinal);
        var pending = new Queue<DocumentDefinition>(roots);
        while (pending.TryDequeue(out var definition))
        {
            foreach (var target in graph.For(definition.Document).Select(static edge => edge switch
                     {
                         DocumentEdge.Dependency dependency => dependency.Target.Value,
                         DocumentEdge.NarrativeReference { Target: NarrativeTarget.Document document } =>
                             document.DocumentGid.Value,
                         DocumentEdge.NarrativeReference { Target: NarrativeTarget.Describe describe } =>
                             describe.DocumentGid.Value,
                         _ => null,
                     }).Where(static target => target is not null))
            {
                var dependency = byGid[target!];
                if (selected.TryAdd(target!, dependency))
                {
                    pending.Enqueue(dependency);
                }
            }
        }

        return selected.Values.ToArray();
    }

    private static void CopyRepositoryLibrary(
        string destinationRoot,
        bool includeBackfill = true)
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation);
        if (includeBackfill)
        {
            var ledgerSources = repository.EnumerateFiles(
                RepositoryRelativePath.Create("Meta/Digestion/backfill"), "*");
            foreach (var source in ledgerSources)
            {
                var destination = Path.Combine(destinationRoot, source.Value);
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                repository.CopyTo(source, destination);
            }
        }

        foreach (var source in repository.EnumerateFiles(
                     RepositoryRelativePath.Create("Library"), "*.md"))
        {
            var destination = Path.Combine(destinationRoot, source.Value);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            repository.CopyTo(source, destination);
        }
    }

    private static void CopyProjectionFixtures(string destinationRoot)
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintInvalidOperation);
        var destinationDirectory = Path.Combine(destinationRoot, "Golden", "Projection");
        TemporaryFileSystem.Directory.CreateDirectory(destinationDirectory);
        foreach (var source in repository.EnumerateFiles(
                     RepositoryRelativePath.Create("Golden/Projection"), "*.json"))
        {
            repository.CopyTo(
                source,
                Path.Combine(destinationDirectory, Path.GetFileName(source.Value)),
                overwrite: true);
        }

        // The projection loader reads this report when it exists, on top of the pinned
        // Golden/Projection fixtures. Copy it so a local run sees the same inputs as the
        // repository, but do not require it: the engineering CI job builds no Lean report, and a
        // synthetic repository must be constructible without one.
        const string rawReport = ".lake/build/stratalint/raw-lean-report.json";
        var rawReportPath = RepositoryRelativePath.Create(rawReport);
        if (repository.FileExists(rawReportPath))
        {
            var reportDestination = Path.Combine(destinationRoot, rawReport);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(reportDestination)!);
            repository.CopyTo(rawReportPath, reportDestination, overwrite: true);
            var materialArchive = RepositoryRelativePath.Create(rawReport + ".materials.zip");
            if (repository.FileExists(materialArchive))
            {
                repository.CopyTo(
                    materialArchive,
                    reportDestination + ".materials.zip",
                    overwrite: true);
            }
        }
    }
}
