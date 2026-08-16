using System.Collections.Immutable;
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
    {
        return Run(repositoryRoot, check, output, error, LeanCompiledArtifactReports.InspectRepository,
            validateRepository: true, tolerateAbsentDocuments: false, delta: null).ExitCode;
    }

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
            tolerateAbsentDocuments: false,
            delta: null).ExitCode;
    }

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        ScribeDeltaInputs delta)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        ArgumentNullException.ThrowIfNull(delta);
        if (!check)
        {
            throw new ArgumentException("Scribe delta scope is only valid for checks.", nameof(check));
        }
        if (!ScribeDeltaScope.RequiresBlueprintEmission(delta.Changes, delta.ProducerPaths))
        {
            output.WriteLine("checked: 0 blueprint(s)");
            return 0;
        }

        return Run(
            repositoryRoot,
            check,
            output,
            error,
            LeanCompiledArtifactReports.InspectRepository,
            validateRepository: true,
            tolerateAbsentDocuments: false,
            delta).ExitCode;
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
            tolerateAbsentDocuments: false,
            delta: null).ExitCode;
    }

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        ScribeDeltaInputs delta)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(delta);
        if (!check)
        {
            throw new ArgumentException("Scribe delta scope is only valid for checks.", nameof(check));
        }
        if (!ScribeDeltaScope.RequiresBlueprintEmission(delta.Changes, delta.ProducerPaths))
        {
            output.WriteLine("checked: 0 blueprint(s)");
            return 0;
        }

        return Run(
            repositoryRoot,
            check,
            output,
            error,
            _ => leanReport,
            validateRepository: false,
            tolerateAbsentDocuments: false,
            delta).ExitCode;
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
            tolerateAbsentDocuments: true,
            delta: null).Verification;
    }

    private static ScribeEmissionRun Run(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        Func<string, LeanAxiomReport> loadLeanReport,
        bool validateRepository,
        bool tolerateAbsentDocuments,
        ScribeDeltaInputs? delta)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        ArgumentNullException.ThrowIfNull(loadLeanReport);

        try
        {
            var leanReport = loadLeanReport(repositoryRoot);

            // Emission runs against the binary's own tree, where every document's
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
            var repositoryDefinitions = DocumentDefinitions.Discover(
                typeof(DocumentDefinitions).Assembly,
                repositoryRoot);
            if (check && !tolerateAbsentDocuments)
            {
                var blueprintRoot = Path.Combine(repositoryRoot, "Blueprint");
                var sourceFindings = DocumentDefinitions.CheckRepositorySourceBijection(
                    Directory.EnumerateFiles(
                            blueprintRoot,
                            "*.scribe.cs",
                            SearchOption.AllDirectories)
                        .Select(path => Path.GetRelativePath(repositoryRoot, path)),
                    repositoryDefinitions);
                if (sourceFindings.Length != 0)
                {
                    foreach (var finding in sourceFindings)
                    {
                        error.WriteLine(finding);
                    }

                    return new ScribeEmissionRun(1, null);
                }
            }
            var definitions = tolerateAbsentDocuments
                ? repositoryDefinitions
                    .Where(definition => File.Exists(Path.Combine(
                        repositoryRoot,
                        ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value))))
                    .ToArray()
                : [.. repositoryDefinitions];
            var declarationCatalog = DeclarationCatalog.Create(leanReport);
            definitions = definitions
                .Select(definition => definition.ResolveDeclarations(declarationCatalog))
                .ToArray();
            if (tolerateAbsentDocuments && definitions.Length == 0 && !repositoryDefinitions.IsEmpty)
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
                    leanReport,
                    declarationCatalog: declarationCatalog);
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

            var documents = definitions.Select(static definition => definition.Document).ToArray();
            var census = ReceiptFreeDocumentCatalog.Load(
                repositoryRoot,
                documents,
                tolerateAbsentDocuments);
            var graph = DocumentGraphAssembler.Assemble(
                documents,
                declarationCatalog,
                census.ReceiptFreeDocumentGids);
            var deltaDocuments = definitions.Select(static definition => new ScribeDeltaDocument(
                definition.Document.Header.Gid.Value,
                ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value),
                definition.RelativePath.Value)).ToImmutableArray();
            var scope = delta is null
                ? ScribeDeltaScope.Full(deltaDocuments)
                : ScribeDeltaScope.Create(
                    delta.Changes,
                    delta.ProducerPaths,
                    deltaDocuments,
                    DescribeTargetsByDefinition(definitions, graph),
                    BaseDescribeTargets(definitions, delta));
            var wired = documents.Count(document => graph.For(document).Length > 0);
            var graphEdges = documents.SelectMany(document => graph.For(document)).ToArray();
            output.WriteLine(
                $"document graph: receipt-free={census.ReceiptFreeDocumentGids.Count} "
                + $"receipt-bound={census.ReceiptBoundDocumentGids.Count} wired={wired} "
                + $"truth-anchor={graphEdges.OfType<DocumentEdge.TruthAnchor>().Count()} "
                + $"dependency={graphEdges.OfType<DocumentEdge.Dependency>().Count()} "
                + $"narrative={graphEdges.OfType<DocumentEdge.NarrativeReference>().Count()}");
            return EmitVerified(
                repositoryRoot, check, output, error,
                declarationCatalog, definitions, graph, scope);
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
        DeclarationCatalog declarationCatalog,
        IReadOnlyList<DocumentDefinition> definitions,
        DocumentGraph graph,
        ScribeDeltaScope scope)
    {
        var rendered = new List<(DocumentDefinition Definition, byte[] Bytes)>();
        var attestations = new List<ScribeEmissionRecord>();
        var declarationReferences = new HashSet<string>(StringComparer.Ordinal);
        var describeLatexRecords = new List<ScribeDescribeLatexRecord>();
        var citations = LibraryNoteCatalog.Load(repositoryRoot).Citations;
        foreach (var definition in definitions)
        {
            var gid = definition.Document.Header.Gid.Value;
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(gid);
            var emissionPath = definition.RelativePath.Value;
            var bytes = scope.Contains(emissionPath)
                ? CanonicalMarkdownWriter.Write(
                    definition.Document,
                    declarationCatalog,
                    citations,
                    graph).ToArray()
                : ReadTrustedEmission(repositoryRoot, emissionPath);
            if (scope.Contains(emissionPath))
            {
                rendered.Add((definition, bytes));
            }
            var source = File.ReadAllBytes(Path.Combine(repositoryRoot, definitionPath));
            attestations.Add(new ScribeEmissionRecord(
                gid,
                definitionPath,
                DigestionFingerprint.Compute(source).RawSha256,
                definition.RelativePath.Value,
                DigestionFingerprint.Compute(bytes).RawSha256));
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
        // corruption. So an existing attestation diff still fails the emit --check exit code, but must not,
        // on its own, void the per-document capability for the base-owned documents that verified. The
        // attestation is FILEMAP run-local and gitignored, so its absence in a clean checkout is not drift.
        var attestationOutOfDate = false;
        var attestationPath = Path.Combine(repositoryRoot, ScribeEmissionAttestation.RelativePath);
        var attestationExists = File.Exists(attestationPath);
        var currentAttestation = attestationExists
            ? File.ReadAllBytes(attestationPath)
            : [];
        if (!currentAttestation.AsSpan().SequenceEqual(attestationBytes))
        {
            if (check && attestationExists)
            {
                attestationOutOfDate = true;
                error.WriteLine($"out of date: {ScribeEmissionAttestation.RelativePath}");
            }
            else if (!check)
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
            output.WriteLine($"checked: {scope.EmissionPaths.Count} blueprint(s)");
            if (attestationExists)
            {
                output.WriteLine($"checked: {ScribeEmissionAttestation.RelativePath}");
            }
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

    private static byte[] ReadTrustedEmission(string repositoryRoot, string emissionPath)
    {
        var path = Path.Combine(repositoryRoot, emissionPath);
        if (!File.Exists(path))
        {
            throw new InvalidOperationException(
                $"trusted unscoped Scribe emission is absent: {emissionPath}");
        }

        return File.ReadAllBytes(path);
    }

    private static ImmutableDictionary<string, ImmutableHashSet<string>> DescribeTargetsByDefinition(
        IEnumerable<DocumentDefinition> definitions,
        DocumentGraph graph)
    {
        var result = ImmutableDictionary.CreateBuilder<string, ImmutableHashSet<string>>(
            StringComparer.Ordinal);
        foreach (var definition in definitions)
        {
            var targets = graph.ExplicitEdges[definition.Document.Header.Gid.Value]
                .OfType<DocumentEdge.NarrativeReference>()
                .Select(static edge => edge.Target)
                .OfType<NarrativeTarget.Describe>()
                .Select(static target => target.DocumentGid.Value)
                .ToImmutableHashSet(StringComparer.Ordinal);
            result.Add(
                ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value),
                targets);
        }

        return result.ToImmutable();
    }

    private static ImmutableDictionary<string, ImmutableHashSet<string>> BaseDescribeTargets(
        IEnumerable<DocumentDefinition> definitions,
        ScribeDeltaInputs delta)
    {
        var changedDefinitions = delta.Changes.Entries
            .Select(static change => change.Path.Value)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var result = ImmutableDictionary.CreateBuilder<string, ImmutableHashSet<string>>(
            StringComparer.Ordinal);
        foreach (var definition in definitions)
        {
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(
                definition.Document.Header.Gid.Value);
            if (!changedDefinitions.Contains(definitionPath)) continue;
            var markdown = delta.ReadBaseDocument(definition.RelativePath.Value);
            if (markdown is not null)
            {
                result.Add(
                    definitionPath,
                    ScribeBaseDocumentReferences.ParseDescribeTargetGids(markdown));
            }
        }

        return result.ToImmutable();
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
                    latexRecords.Add(new ScribeDescribeLatexRecord(
                        $"{documentGid}#describe/{describe.Id.Value}",
                        definitionPath,
                        DescribeVocabulary.CanonicalName(describe.Kind),
                        describe.Statement is DescribeStatement.FormulaAst
                            || describe.StatementFormula is not null,
                        describe.FormulaProvenance == StatementFormulaProvenance.LeanDerived
                            ? "lean-derived" : "hand-authored",
                        describe.Statement is DescribeStatement.LeanDeclaration lean
                            && StatementProjectionFixtureLoader.Project(lean.Value) is ProjectionOutcome.Unprojectable failed
                                ? failed.Reason : null));
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
