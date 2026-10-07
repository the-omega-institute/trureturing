using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeEmitter
{
    private sealed record ScribeEmissionRun(
        int ExitCode,
        VerifiedScribeEmissions? Verification);


    internal static int EmitPaths(
        string repositoryRoot,
        IEnumerable<string> changedPaths,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        bool validateRepository = false,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        return EmitPaths(repositoryRoot, changedPaths, check, output, error, () => leanReport,
            validateRepository, frozenState, frozenStatements);
    }

    internal static int EmitPaths(
        string repositoryRoot,
        IEnumerable<string> changedPaths,
        bool check,
        TextWriter output,
        TextWriter error,
        Func<LeanAxiomReport> loadLeanReport,
        bool validateRepository = false,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(changedPaths);
        ArgumentNullException.ThrowIfNull(loadLeanReport);
        var changes = changedPaths.ToArray();
        var selection = ScribeDefinitionSelector.Select(repositoryRoot, changes);
        if (!selection.IsSuccess)
        {
            error.WriteLine(selection.Failure);
            return 2;
        }

        var admission = ScribeSdkAdmission.Check(repositoryRoot, selection.Paths);
        if (admission.ExitCode != 0)
        {
            admission.WriteFailure(error);
            return admission.ExitCode;
        }

        if (selection.Paths.IsEmpty)
        {
            output.WriteLine("emitted: 0 changed blueprint(s)");
            return 0;
        }

        var leanReport = loadLeanReport();
        return StatementProjectionFixtureLoader.WithFreshRepositoryRoot(repositoryRoot, () =>
        {
            var results = ScribeScriptHost.ExecuteBatch(repositoryRoot, selection.Paths);
            var failures = results.Where(static result => !result.IsSuccess).ToArray();
            if (failures.Length != 0)
            {
                foreach (var failure in failures)
                    error.WriteLine(failure.Failure);
                return 1;
            }

            // The resource boundary is deliberate: scoped emission consumes the same
            // strongly typed bytes that a release consumer reads.
            var definitions = results
                .Select(static result => ScribeResourceCodec.Decode(
                    ScribeResourceCodec.Encode(result.Definition!),
                    expectedGid: result.Definition!.Document.Header.Gid.Value,
                    expectedSourcePath: result.RelativePath))
                .ToArray();
            return Run(
                repositoryRoot,
                check,
                output,
                error,
                _ => leanReport,
                validateRepository,
                frozenState: frozenState, frozenStatements: frozenStatements,
                suppliedDefinitions: definitions,
                writeAttestation: false,
                checkFreshness: check,
                graphRepositoryRoot: repositoryRoot,
                validateDocumentGraph: false,
                validateSourceBijection: false).ExitCode;
        });
    }

    internal static int Emit(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        IReadOnlyList<DocumentDefinition> definitions,
        bool scoped = false, bool validateRepository = false,
        FrozenStateCatalog? frozenState = null, FrozenStatementIndex? frozenStatements = null)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(definitions);
        return Run(
            repositoryRoot,
            check,
            output,
            error,
            _ => leanReport,
            validateRepository, suppliedDefinitions: definitions,
            frozenState: frozenState, frozenStatements: frozenStatements,
            writeAttestation: !scoped, graphRepositoryRoot: scoped ? repositoryRoot : null,
            validateDocumentGraph: !scoped, validateSourceBijection: !scoped).ExitCode;
    }

    /// <summary>Checks rendered and tracked markdown formulas in the caller's scope.</summary>
    internal static int CheckMarkdown(
        string repositoryRoot,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport leanReport,
        MarkdownFormulaScope scope,
        IReadOnlyList<DocumentDefinition> definitions,
        bool scoped = false)
    {
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(scope);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        var run = scoped && definitions.Count == 0 ? new ScribeEmissionRun(0, null) : Run(
            repositoryRoot,
            check: true,
            TextWriter.Null,
            error,
            _ => leanReport,
            validateRepository: false,
            suppliedDefinitions: definitions,
            markdownScope: scope,
            writeAttestation: !scoped,
            graphRepositoryRoot: scoped ? repositoryRoot : null,
            validateDocumentGraph: !scoped,
            validateSourceBijection: !scoped);
        if (run.ExitCode != 0)
        {
            return run.ExitCode;
        }

        if (scoped && definitions.Count == 0) scope.Close();

        foreach (var finding in scope.Findings)
        {
            error.WriteLine($"markdown red {finding}");
        }

        output.WriteLine(
            $"markdown: judged={scope.Judged} formula(s)={scope.Formulas} "
            + $"red={scope.Findings.Length}");
        return scope.Findings.IsEmpty ? 0 : 1;
    }

    internal static VerifiedScribeEmissions? Verify(string repositoryRoot, TextWriter error,
        LeanAxiomReport report, IReadOnlyList<DocumentDefinition> definitions,
        FrozenStateCatalog? frozenState = null, FrozenStatementIndex? frozenStatements = null, bool scoped = false) =>
        Run(repositoryRoot, check: true, TextWriter.Null, error, _ => report,
            validateRepository: true, suppliedDefinitions: definitions,
            frozenState: frozenState, frozenStatements: frozenStatements,
            writeAttestation: !scoped, graphRepositoryRoot: scoped ? repositoryRoot : null,
            validateDocumentGraph: !scoped, validateSourceBijection: false).Verification;

    private static ScribeEmissionRun Run(
        string repositoryRoot,
        bool check,
        TextWriter output,
        TextWriter error,
        Func<string, LeanAxiomReport> loadLeanReport,
        bool validateRepository,
        IReadOnlyList<DocumentDefinition>? suppliedDefinitions = null,
        MarkdownFormulaScope? markdownScope = null,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null,
        bool writeAttestation = true,
        bool checkFreshness = false,
        string? graphRepositoryRoot = null,
        bool validateDocumentGraph = true,
        bool validateSourceBijection = true)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);
        ArgumentNullException.ThrowIfNull(loadLeanReport);
        ArgumentNullException.ThrowIfNull(suppliedDefinitions);

        try
        {
            var leanReport = loadLeanReport(repositoryRoot);

            var repositoryDefinitions = suppliedDefinitions;
            if (check && validateSourceBijection)
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
            var definitions = repositoryDefinitions.ToArray();
            var declarationCatalog = DeclarationCatalog.Create(leanReport);
            definitions = definitions
                .Select(definition => definition.ResolveDeclarations(declarationCatalog))
                .ToArray();
            if (validateRepository)
            {
                var findings = DescribeRepositoryValidator.Validate(
                    repositoryRoot,
                    definitions.Select(static definition => definition.Document),
                    leanReport,
                    declarationCatalog: declarationCatalog,
                    frozenState: frozenState,
                    frozenStatements: frozenStatements,
                    singleDocument: !validateDocumentGraph);
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
                tolerateAbsentDocuments: false);
            var graph = DocumentGraphAssembler.Assemble(
                documents,
                declarationCatalog,
                graphRepositoryRoot,
                validateDocumentGraph);
            if (!graph.Findings.IsEmpty)
            {
                foreach (var finding in graph.Findings)
                    error.WriteLine(
                        $"describe red code={finding.Code} path={finding.Path} message={finding.Message}");
                return new ScribeEmissionRun(1, null);
            }
            var wired = documents.Count(document => graph.For(document).Length > 0);
            var graphEdges = documents.SelectMany(document => graph.For(document)).ToArray();
            output.WriteLine(
                $"document graph: receipt-free={census.ReceiptFreeDocumentGids.Count} "
                + $"receipt-bound={census.ReceiptBoundDocumentGids.Count} wired={wired} "
                + $"truth-anchor={graphEdges.OfType<DocumentEdge.TruthAnchor>().Count()} "
                + $"dependency={graphEdges.OfType<DocumentEdge.Dependency>().Count()} "
                + $"narrative={graphEdges.OfType<DocumentEdge.NarrativeReference>().Count()}");
            if (markdownScope is not null)
            {
                var citations = LibraryNoteCatalog.Load(repositoryRoot).Citations;
                markdownScope.Judge(
                    definitions,
                    definition => CanonicalMarkdownWriter.Write(
                        definition.Document,
                        declarationCatalog,
                        citations,
                        graph).AsMemory());
                return new ScribeEmissionRun(0, null);
            }

            return EmitVerified(
                repositoryRoot, check, output, error,
                declarationCatalog, definitions, graph, writeAttestation, checkFreshness);
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
        bool writeAttestation = true,
        bool checkFreshness = false)
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

        if (check && checkFreshness)
        {
            var mismatches = rendered
                .Where(item => !File.Exists(Path.Combine(repositoryRoot, item.Definition.RelativePath.Value))
                    || !File.ReadAllBytes(Path.Combine(repositoryRoot, item.Definition.RelativePath.Value))
                        .AsSpan().SequenceEqual(item.Bytes))
                .Select(item => item.Definition.RelativePath.Value)
                .Order(StringComparer.Ordinal)
                .ToArray();
            foreach (var path in mismatches)
                error.WriteLine($"md mismatch: {path}");
            if (mismatches.Length != 0)
                return new ScribeEmissionRun(1, null);
        }

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

        if (!check && writeAttestation)
        {
            var attestationPath = Path.Combine(repositoryRoot, GeneratedArtifactInventory.ScribeAttestation.Path);
            var currentAttestation = File.Exists(attestationPath)
                ? File.ReadAllBytes(attestationPath)
                : [];
            if (!currentAttestation.AsSpan().SequenceEqual(attestationBytes))
            {
                var parent = Path.GetDirectoryName(attestationPath)
                    ?? throw new InvalidOperationException("Scribe attestation path has no parent directory.");
                Directory.CreateDirectory(parent);
                File.WriteAllBytes(attestationPath, attestationBytes);
                output.WriteLine($"wrote: {GeneratedArtifactInventory.ScribeAttestation.Path}");
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
