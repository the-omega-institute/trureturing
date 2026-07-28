using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeEmitter
{
    private sealed record ScribeEmissionRun(
        int ExitCode,
        VerifiedScribeEmissions? Verification);

    internal static string AttestationRelativePath => ScribeEmissionAttestation.RelativePath;

    public static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error)
        => Run(
            repositoryRoot,
            check,
            output,
            error,
            LeanCompiledArtifactReports.InspectRepository,
            validateRepository: true,
            tolerateAbsentDocuments: false).ExitCode;

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return Run(
            repositoryRoot,
            check,
            output,
            error,
            _ => leanReport,
            validateRepository: false,
            tolerateAbsentDocuments: false).ExitCode;
    }

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        bool validateRepository)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return Run(
            repositoryRoot,
            check,
            output,
            error,
            _ => leanReport,
            validateRepository,
            tolerateAbsentDocuments: false).ExitCode;
    }

    internal static VerifiedScribeEmissions? Verify(
        string repositoryRoot,
        TextWriter error,
        LeanAxiomReport leanReport)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return Run(
            repositoryRoot,
            check: true,
            TextWriter.Null,
            error,
            _ => leanReport,
            validateRepository: true,
            tolerateAbsentDocuments: true).Verification;
    }

    private static ScribeEmissionRun Run(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        Func<string, LeanAxiomReport> loadLeanReport,
        bool validateRepository,
        bool tolerateAbsentDocuments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        ArgumentNullException.ThrowIfNull(loadLeanReport);

        try
        {
            var leanReport = loadLeanReport(repositoryRoot);

            // Emission (make emit / emit-check) runs against the binary's own tree, where every document's
            // .scribe.cs source must be present; a missing source there is a real fault, so the strict path
            // keeps the full DocumentDefinitions.All (an absent source dangling-fails or "emit failed").
            //
            // Capability verification (Verify), by contrast, judges an arbitrary tree that may predate some
            // of this binary's documents. A document this binary knows about is only materialized in that
            // tree when its .scribe.cs source is present. During conservative-extension replay the candidate
            // harness re-judges the baseline tree, which lacks a newly added Blueprint's source entirely;
            // that document is a not-yet-materialized protected-surface addition (SL-022 routes its
            // .scribe.cs to Component C), not part of this tree — so it must not be dangling-flagged, read,
            // attested, or counted, which would make the candidate block a tree the baseline admits.
            // A document whose source IS present stays in scope: a present source with a missing or
            // mismatched .md is a real out-of-date/corruption and still voids the capability below
            // (deleted or forged base-owned emissions are caught locally, not laundered through this skip).
            var definitions = tolerateAbsentDocuments
                ? DocumentDefinitions.All
                    .Where(definition => File.Exists(Path.Combine(
                        repositoryRoot,
                        ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value))))
                    .ToArray()
                : [.. DocumentDefinitions.All];
            if (tolerateAbsentDocuments && definitions.Length == 0 && !DocumentDefinitions.All.IsEmpty)
            {
                // A tree owning zero of this binary's documents is not an older world of this
                // repository at all (wrong root, gutted checkout): verifying it vacuously would
                // hide the fault behind distant digestion gaps — fail loud at the source instead.
                throw new InvalidOperationException(
                    $"no Scribe definition sources found under {repositoryRoot}");
            }
            if (validateRepository)
            {
                var findings = DescribeRepositoryValidator.Validate(
                    repositoryRoot,
                    definitions.Select(static definition => definition.Document),
                    leanReport);
                if (!findings.IsEmpty)
                {
                    foreach (var finding in findings)
                    {
                        error.WriteLine(
                            $"describe red code={finding.Code} path={finding.Path} message={finding.Message}");
                    }

                    return new ScribeEmissionRun(1, null);
                }
            }

            return EmitVerified(repositoryRoot, check, output, error, leanReport, definitions);
        }
        catch (Exception exception) when (
            exception is InvalidOperationException
                or FormatException
                or IOException
                or UnauthorizedAccessException
                or ArgumentException)
        {
            error.WriteLine($"emit failed: {exception.Message}");
            return new ScribeEmissionRun(1, null);
        }
    }

    private static ScribeEmissionRun EmitVerified(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        IReadOnlyList<DocumentDefinition> definitions)
    {
        var rendered = new List<(DocumentDefinition Definition, byte[] Bytes)>();
        var attestations = new List<ScribeEmissionRecord>();
        var declarationReferences = new HashSet<string>(StringComparer.Ordinal);
        var describeLatexRecords = new List<ScribeDescribeLatexRecord>();
        var citations = LibraryNoteCatalog.Load(repositoryRoot).Citations;
        foreach (var definition in definitions)
        {
            var first = CanonicalMarkdownWriter.Write(
                definition.Document,
                leanReport,
                citations).ToArray();
            var second = CanonicalMarkdownWriter.Write(
                definition.Document,
                leanReport,
                citations).ToArray();
            if (!first.AsSpan().SequenceEqual(second))
            {
                throw new InvalidOperationException(
                    $"Scribe rendering is not deterministic for {definition.Document.Header.Gid.Value}.");
            }

            rendered.Add((definition, first));
            var gid = definition.Document.Header.Gid.Value;
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(gid);
            var source = File.ReadAllBytes(Path.Combine(repositoryRoot, definitionPath));
            attestations.Add(new ScribeEmissionRecord(
                gid,
                definitionPath,
                DigestionFingerprint.Compute(source).RawSha256,
                definition.RelativePath.Value,
                DigestionFingerprint.Compute(first).RawSha256));
            CollectDescribeCapabilities(
                gid,
                definitionPath,
                definition.Document.Content,
                declarationReferences,
                describeLatexRecords);
        }

        var attestationBytes = ScribeEmissionAttestation.Write(attestations).ToArray();

        // documentDifferences counts only base-owned emissions (documents compiled into this binary's
        // DocumentDefinitions.All) whose render disagrees with the on-disk .md. When this binary is the
        // dev-baseline harness judging a candidate, DocumentDefinitions.All is exactly the base-owned set;
        // a base-owned emission mismatch is therefore real corruption and must void the capability.
        var documentDifferences = 0;
        var writes = 0;
        foreach (var (definition, expected) in rendered)
        {
            var path = Path.Combine(repositoryRoot, definition.RelativePath.Value);
            var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
            if (current.AsSpan().SequenceEqual(expected))
            {
                continue;
            }

            if (check)
            {
                documentDifferences++;
                error.WriteLine($"out of date: {definition.RelativePath.Value}");
                continue;
            }

            var parent = Path.GetDirectoryName(path)
                ?? throw new InvalidOperationException("Blueprint path has no parent directory.");
            Directory.CreateDirectory(parent);
            File.WriteAllBytes(path, expected);
            writes++;
            output.WriteLine($"wrote: {definition.RelativePath.Value}");
        }

        // The attestation covers every on-disk Blueprint scribe, including candidate-only documents this
        // binary cannot render (their .scribe.cs is absent from DocumentDefinitions.All). A candidate that
        // adds such a document produces an attestation this base binary cannot reproduce byte-for-byte, yet
        // that is a protected-surface signal (SL-022 routes the new .scribe.cs to Component C), not base-owned
        // corruption. So the attestation diff still fails the emit --check exit code (kept strict below) but
        // must not, on its own, void the per-document capability for the base-owned documents that verified.
        var attestationOutOfDate = false;
        var attestationPath = Path.Combine(repositoryRoot, ScribeEmissionAttestation.RelativePath);
        var currentAttestation = File.Exists(attestationPath)
            ? File.ReadAllBytes(attestationPath)
            : [];
        if (!currentAttestation.AsSpan().SequenceEqual(attestationBytes))
        {
            if (check)
            {
                attestationOutOfDate = true;
                error.WriteLine($"out of date: {ScribeEmissionAttestation.RelativePath}");
            }
            else
            {
                var parent = Path.GetDirectoryName(attestationPath)
                    ?? throw new InvalidOperationException("Scribe attestation path has no parent directory.");
                Directory.CreateDirectory(parent);
                File.WriteAllBytes(attestationPath, attestationBytes);
                output.WriteLine($"wrote: {ScribeEmissionAttestation.RelativePath}");
            }
        }

        var differences = documentDifferences + (attestationOutOfDate ? 1 : 0);
        if (check && differences == 0)
        {
            output.WriteLine($"checked: {definitions.Count} blueprint(s)");
            output.WriteLine($"checked: {ScribeEmissionAttestation.RelativePath}");
        }
        else if (!check)
        {
            output.WriteLine($"emitted: {writes} changed blueprint(s)");
        }

        return new ScribeEmissionRun(
            differences == 0 ? 0 : 1,
            check && documentDifferences == 0
                ? VerifiedScribeEmissions.Create(
                    attestations,
                    declarationReferences,
                    describeLatexRecords)
                : null);
    }

    private static void CollectDescribeCapabilities(
        string documentGid,
        string definitionPath,
        BlockSequence blocks,
        ISet<string> references,
        ICollection<ScribeDescribeLatexRecord> latexRecords)
    {
        foreach (var block in blocks.Items)
        {
            switch (block)
            {
                case DocumentBlock.Section section:
                    CollectDescribeCapabilities(
                        documentGid,
                        definitionPath,
                        section.Content,
                        references,
                        latexRecords);
                    break;
                case DocumentBlock.Describe describe:
                    if (describe.Statement is DescribeStatement.LeanDeclaration declaration)
                    {
                        references.Add(declaration.Value.Value);
                    }
                    var requiresLatex = describe.Kind is DescribeKind.Theorem
                        or DescribeKind.Proposition
                        or DescribeKind.Lemma;
                    latexRecords.Add(new ScribeDescribeLatexRecord(
                        $"{documentGid}#describe/{describe.Id.Value}",
                        definitionPath,
                        requiresLatex,
                        describe.Statement is DescribeStatement.FormulaAst
                            || describe.StatementLatex is not null));
                    CollectDescribeCapabilities(
                        documentGid,
                        definitionPath,
                        describe.Content,
                        references,
                        latexRecords);
                    break;
            }
        }
    }
}
