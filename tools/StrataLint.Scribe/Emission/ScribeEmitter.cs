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
            validateRepository: true, tolerateAbsentDocuments: false).ExitCode;
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

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        IReadOnlyList<DocumentDefinition> definitions)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(definitions);
        return Run(
            repositoryRoot,
            check,
            output,
            error,
            _ => leanReport,
            validateRepository: false,
            tolerateAbsentDocuments: false,
            suppliedDefinitions: definitions).ExitCode;
    }

    /// <summary>
    /// Puts the formulas of the markdown a change touches in front of the pinned KaTeX,
    /// on both the committed bytes and the current render. The corpus is still rendered —
    /// a document's bytes depend on the whole document graph — but only the named
    /// projections are judged and reported, and freshness stays ungated.
    /// </summary>
    internal static int CheckMarkdown(
        string repositoryRoot,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        MarkdownFormulaScope scope)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(scope);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        var run = Run(
            repositoryRoot,
            check: true,
            TextWriter.Null,
            error,
            _ => leanReport,
            validateRepository: false,
            tolerateAbsentDocuments: false,
            markdownScope: scope);
        if (run.ExitCode != 0)
        {
            return run.ExitCode;
        }

        scope.Close();
        foreach (var finding in scope.Findings)
        {
            error.WriteLine($"markdown red {finding}");
        }

        output.WriteLine(
            $"markdown: judged={scope.Judged} formula(s)={scope.Formulas} "
            + $"red={scope.Findings.Length}");
        return scope.Findings.IsEmpty ? 0 : 1;
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
        bool tolerateAbsentDocuments,
        IReadOnlyList<DocumentDefinition>? suppliedDefinitions = null,
        MarkdownFormulaScope? markdownScope = null)
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
            // A document whose source IS present stays in scope. The capability is issued from the
            // current validated render and never from tracked reader-snapshot bytes.
            var repositoryDefinitions = suppliedDefinitions ?? DocumentDefinitions.Discover(
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
            if (tolerateAbsentDocuments && definitions.Length == 0 && repositoryDefinitions.Count != 0)
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
                declarationCatalog);
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
                declarationCatalog, definitions, graph, markdownScope);
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
        MarkdownFormulaScope? markdownScope)
    {
        var rendered = new List<(DocumentDefinition Definition, byte[] Bytes)>();
        var attestations = new List<ScribeEmissionRecord>();
        var declarationReferences = new HashSet<string>(StringComparer.Ordinal);
        var describeLatexRecords = new List<ScribeDescribeLatexRecord>();
        var citations = LibraryNoteCatalog.Load(repositoryRoot).Citations;
        foreach (var definition in definitions)
        {
            var bytes = CanonicalMarkdownWriter.Write(
                definition.Document,
                declarationCatalog,
                citations,
                graph).ToArray();

            rendered.Add((definition, bytes));
            markdownScope?.Inspect(definition, bytes);
            var gid = definition.Document.Header.Gid.Value;
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(gid);
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

        var writes = 0;
        if (!check)
        {
            foreach (var (definition, expected) in rendered)
            {
                var path = Path.Combine(repositoryRoot, definition.RelativePath.Value);
                var current = File.Exists(path) ? File.ReadAllBytes(path) : [];
                if (current.AsSpan().SequenceEqual(expected))
                {
                    continue;
                }

                var parent = Path.GetDirectoryName(path)
                    ?? throw new InvalidOperationException("Blueprint path has no parent directory.");
                Directory.CreateDirectory(parent);
                File.WriteAllBytes(path, expected);
                writes++;
                output.WriteLine($"wrote: {definition.RelativePath.Value}");
            }
        }

        if (!check)
        {
            var attestationPath = Path.Combine(repositoryRoot, ScribeEmissionAttestation.RelativePath);
            var currentAttestation = File.Exists(attestationPath)
                ? File.ReadAllBytes(attestationPath)
                : [];
            if (!currentAttestation.AsSpan().SequenceEqual(attestationBytes))
            {
                var parent = Path.GetDirectoryName(attestationPath)
                    ?? throw new InvalidOperationException("Scribe attestation path has no parent directory.");
                Directory.CreateDirectory(parent);
                File.WriteAllBytes(attestationPath, attestationBytes);
                output.WriteLine($"wrote: {ScribeEmissionAttestation.RelativePath}");
            }
        }

        if (check)
        {
            output.WriteLine($"verified: {definitions.Count} current blueprint render(s)");
        }
        else
        {
            output.WriteLine($"emitted: {writes} changed blueprint(s)");
        }

        return new ScribeEmissionRun(
            0,
            VerifiedScribeEmissions.Create(
                attestations,
                declarationReferences,
                describeLatexRecords));
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
