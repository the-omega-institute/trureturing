using System.Collections.Immutable;
using System.Reflection;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe.Tests;

public sealed class DocumentDiscoveryTests
{
    private const string PhaseSourcePath = "Blueprint/D5/S1/Phase/Basic.scribe.cs";

    [Fact]
    public void RepositoryBijectionFailuresNameTheUnregisteredSourceAndProjectionRepair()
    {
        var registered = DocumentDefinitions.All;
        var filesystemSources = registered
            .Select(static definition =>
                ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value))
            .Append("Blueprint/D5/S9/Synthetic/Unregistered.scribe.cs")
            .ToArray();

        var findings = DocumentDefinitions.CheckRepositorySourceBijection(
            filesystemSources,
            registered);

        Assert.Equal(
            ["unregistered Scribe source: Blueprint/D5/S9/Synthetic/Unregistered.scribe.cs"],
            findings);
        Assert.Equal(
            ["required Markdown projection is missing: Blueprint/D5/S9/Synthetic/Missing.md; "
                + "run make emit and commit Blueprint/D5/S9/Synthetic/Missing.md"],
            MarkdownProjectionBijectionFindings(
                ["Blueprint/D5/S9/Synthetic/Missing.md"],
                []));
    }

    [Fact]
    public void EmptyProjectionAssertionPreservesTheCompleteRepairMessage()
    {
        const string missing = "Blueprint/D5/S9/Synthetic/Missing.md";
        var findings = MarkdownProjectionBijectionFindings([missing], []);

        var exception = Record.Exception(() => AssertNoMarkdownProjectionBijectionFindings(findings));

        Assert.NotNull(exception);
        Assert.Contains(missing, exception.Message, StringComparison.Ordinal);
        Assert.Contains("run make emit and commit", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReflectionDiscoveryIsDeterministic()
    {
        var assembly = typeof(DocumentDefinitions).Assembly;

        var first = DocumentDefinitions.Discover(assembly);
        var second = DocumentDefinitions.Discover(assembly);

        Assert.Equal(
            first.Select(static item => (item.Document.Header.Gid.Value, item.SourcePath)),
            second.Select(static item => (item.Document.Header.Gid.Value, item.SourcePath)));
    }

    [Fact]
    public void DiscoveryRejectsDefinitionWhoseGidDoesNotMatchItsSourcePath()
    {
        var exception = Assert.Throws<InvalidOperationException>(
            () => DocumentDefinitions.Discover(Assembly.GetExecutingAssembly()));

        Assert.Contains("D5/S1/Phase/Basic", exception.Message, StringComparison.Ordinal);
        Assert.Contains(
            PhaseSourcePath,
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RepositoryBijectionsHoldAndScribeEmitterRendersEachDocumentOnlyOnce()
    {
        var repository = RepositoryAccessor.Discover(
            RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);
        var definitions = DocumentDefinitions.All;
        var sources = repository.EnumerateFiles(
            RepositoryRelativePath.Create("Blueprint"),
            "*.scribe.cs");
        Assert.Empty(DocumentDefinitions.CheckRepositorySourceBijection(
            sources.Select(static path => path.Value),
            definitions));
        AssertNoMarkdownProjectionBijectionFindings(MarkdownProjectionBijectionFindings(
            definitions.Select(static definition => definition.RelativePath.Value),
            repository.EnumerateFiles(RepositoryRelativePath.Create("Blueprint"), "*.md")
                .Select(static path => path.Value)));

        var emitterSource = repository.ReadAllText(RepositoryRelativePath.Create(
            "tools/StrataLint.Scribe/Emission/ScribeEmitter.cs"));

        var emitVerified = MethodBody(
            emitterSource,
            "private static ScribeEmissionRun EmitVerified(",
            "private static void CollectDescribeCapabilities(");

        Assert.Equal(1, Occurrences(emitVerified, "CanonicalMarkdownWriter.Write("));

        static int Occurrences(string source, string fragment) =>
            (source.Length - source.Replace(fragment, string.Empty, StringComparison.Ordinal).Length)
            / fragment.Length;

        static string MethodBody(string source, string startMarker, string endMarker)
        {
            var start = source.LastIndexOf(startMarker, StringComparison.Ordinal);
            var end = source.IndexOf(endMarker, start, StringComparison.Ordinal);
            Assert.True(start >= 0 && end > start);
            return source[start..end];
        }
    }

    private static string[] MarkdownProjectionBijectionFindings(
        IEnumerable<string> requiredPaths,
        IEnumerable<string> actualPaths)
    {
        var required = requiredPaths.ToHashSet(StringComparer.Ordinal);
        var actual = actualPaths.ToHashSet(StringComparer.Ordinal);
        return required
            .Except(actual, StringComparer.Ordinal)
            .Select(static path => $"required Markdown projection is missing: {path}; "
                + $"run make emit and commit {path}")
            .Concat(actual
                .Except(required, StringComparer.Ordinal)
                .Select(static path => $"Markdown projection has no Scribe definition: {path}"))
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static void AssertNoMarkdownProjectionBijectionFindings(
        IReadOnlyCollection<string> findings)
    {
        var completeMessage = string.Join(" | ", findings);
        Assert.True(findings.Count == 0, completeMessage);
    }

    [Fact]
    public void GeneratedDocumentGraphMatchesFormalTruth()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);
        var repositoryRoot = repository.Root.FullPath;
        var requireLiveReport = Environment.GetEnvironmentVariable("STRATALINT_REQUIRE_LIVE_REPORT") == "1";
        var hasLiveReport = repository.FileExists(RepositoryRelativePath.Create(
                ".lake/build/stratalint/raw-lean-report.json"))
            && repository.FileExists(RepositoryRelativePath.Create(
                ".lake/build/stratalint/raw-lean-report.json.materials.zip"));
        Assert.True(
            !requireLiveReport || hasLiveReport,
            "STRATALINT_REQUIRE_LIVE_REPORT=1 requires .lake/build/stratalint/raw-lean-report.json");

        Assert.NotEmpty(DocumentDefinitions.All);
        var documents = DocumentDefinitions.All
            .Select(static definition => definition.Document)
            .ToArray();
        var report = hasLiveReport
            ? LeanCompiledArtifactReports.InspectRepository(repositoryRoot)
            : LeanReportFixture.ForDocuments(documents);
        var census = ReceiptFreeDocumentCatalog.Load(repositoryRoot, documents);
        var graph = DocumentGraphAssembler.Assemble(
            documents,
            DeclarationCatalog.Create(report));
        var projection = DocumentGraphExportProjection.Create(
            DocumentDefinitions.All.Select(definition => new DocumentGraphDocument(
                definition.RelativePath.Value,
                definition.Document,
                census.ReceiptFreeDocumentGids.Contains(definition.Document.Header.Gid.Value)
                    ? "receipt-free"
                    : "receipt-bound")),
            graph,
            DeclarationCatalog.Create(report),
            report.Files.Keys.Select(static path => path.Value).ToHashSet(StringComparer.Ordinal));

        Assert.Equal(DocumentDefinitions.All.Length, projection.Documents.Nodes.Length);
        Assert.Equal(
            documents.SelectMany(document => graph.For(document)).OfType<DocumentEdge.TruthAnchor>().Count(),
            projection.Joins.TruthAnchors.Length);
        Assert.All(projection.Joins.TruthAnchors, anchor =>
        {
            Assert.Contains(projection.Documents.Nodes, node =>
                node.RepoPath == anchor.DocumentRepoPath && node.Gid == anchor.DocumentGid);
            Assert.Contains(anchor.FormalTruthRepoPath, report.Files.Keys.Select(static path => path.Value));
        });

    }
    [Fact]
    public void DigitRawContainsATypedRepoDerivedZeckendorfExample()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Digit/Raw");
        var report = LeanReportFixture.ForDocuments([definition.Document]);

        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(
                definition.Document,
                DeclarationCatalog.Create(report),
                RepositoryCitations()).AsSpan());

        Assert.Contains(
            "\\operatorname{Z}\\left(89\\right) + \\operatorname{Z}\\left(34\\right) = \\operatorname{Z}\\left(123\\right) = 1010000000_{W}",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "*Source.* Repository-derived.",
            markdown,
            StringComparison.Ordinal);
    }

    [Fact]
    public void PhaseBasicCarriesInjectivityAsItsTypedLeanStatement()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Phase/Basic");
        var statement = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .Single(static describe => describe.Title.Value == "Injectivity");
        var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(statement.Statement);

        Assert.Equal(
            "D5/S1/Phase/Basic.goldenPhase_injective",
            lean.Value.Value);
        DocumentFactAssertions.Declaration(statement, LeanDeclarationKind.Theorem);
    }

    [Fact]
    public void ZeroOrbitCongruenceCarriesTwoTheoremsAndDisclosesTheLocalPremise()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Phase/ZeroOrbitCongruence");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(2, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });
        Assert.Equal(
            [
                "D5/S1/Phase/ZeroOrbitCongruence.eisenstein_norm_mod_three",
                "D5/S1/Phase/ZeroOrbitCongruence.thirty_six_dvd_of_local_candidates_and_eisenstein_norm",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));

    }

    [Fact]
    public void SeatTowerCombinatoricsCarriesSixTheoremsAndDisclosesItsModelBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Phase/SeatTowerCombinatorics");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(6, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });
        Assert.Equal(
            [
                "D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity",
                "D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd",
                "D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count",
                "D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count",
                "D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique",
                "D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));

    }

    [Fact]
    public void SeatTowerConsequencesCarriesSixTheoremsAndDisclosesReductionBoundaries()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Phase/SeatTowerConsequences");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(6, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });
        Assert.Equal(
            [
                "D5/S1/Phase/SeatTowerConsequences.mod_ninety_six_refines_twenty_four_and_forty_eight",
                "D5/S1/Phase/SeatTowerConsequences.jacobi_factorization_of_selector_numerator",
                "D5/S1/Phase/SeatTowerConsequences.cosecant_peak_identity",
                "D5/S1/Phase/SeatTowerConsequences.dominant_term_gap_bound",
                "D5/S1/Phase/SeatTowerConsequences.singleton_stationing_choice_count",
                "D5/S1/Phase/SeatTowerConsequences.three_split_primes_have_three_singleton_choices",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));

    }

    [Fact]
    public void PrimeAxisTableCarriesItsExactRepoDerivedLeanStatement()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Digit/PrimeAxisTable");
        var describe = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .Single();
        var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);

        Assert.Equal(DescribeKind.Theorem, describe.Kind);
        DocumentFactAssertions.RepoDerived(describe);
        Assert.Null(describe.LiteratureReference);
        Assert.Equal(
            "D5/S1/Digit/PrimeAxisTable.prime_axis_table_spec",
            lean.Value.Value);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
    }

    [Fact]
    public void SelectedResidualDocumentsCarryExactStatementsAndDiligentProvenance()
    {
        (string Document, string Id, DescribeKind Kind, string Declaration,
            LeanDeclarationKind FormalKind,
            DescribeProvenanceKind Provenance, string? Reference)[] expected =
        [
            ("D5/S0/Carrier/AlgebraicModel", "quadratic-quotient-conjugation-trace-and-norm",
                DescribeKind.Definition,
                "D5/S0/Carrier/AlgebraicModel.golden_algebraic_model_spec",
                LeanDeclarationKind.Theorem,
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/stewarttall2025algebraic"),
            ("D5/S0/Carrier/Norm", "norm-euclidean-division",
                DescribeKind.Theorem,
                "D5/S0/Carrier/Euclidean.golden_division",
                LeanDeclarationKind.Theorem,
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/Carrier/chatland1949euclidean"),
            ("D5/S1/Depth/JointDepth", "admissible-joint-scale-digit-phase-depth",
                DescribeKind.Definition,
                "D5/S1/Depth/JointDepth.joint_depth_spec",
                LeanDeclarationKind.Theorem,
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S1/Digit/PrimeAxisAddition", "prime-axis-rowwise-normalization-product",
                DescribeKind.Theorem,
                "D5/S1/Digit/PrimeAxisAddition.prime_axis_addition_spec",
                LeanDeclarationKind.Theorem,
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S1/Scale/MinkowskiModelSet", "minkowski-lattice-window-and-labeled-model-set",
                DescribeKind.Definition,
                "D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec",
                LeanDeclarationKind.Theorem,
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/baakefrankgrimm2021three"),
        ];
        var report = LeanAxiomReport.Create(expected
            .GroupBy(item => DeclarationHandle.Create(item.Declaration).Reference!.Path.Value,
                StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => new LeanFileReport(
                    [],
                    group.Select(static item => new LeanDeclaration(
                            item.Declaration.Replace('/', '.'),
                            item.FormalKind switch
                            {
                                LeanDeclarationKind.Theorem => "theorem",
                                LeanDeclarationKind.Definition => "def",
                                _ => throw new InvalidOperationException(
                                    $"Unsupported fixture declaration kind {item.FormalKind}."),
                            },
                            $"statement-v1(source={item.Declaration})",
                            ImmutableArray.Create("propext", "Classical.choice", "Quot.sound")))
                        .ToImmutableArray()),
                StringComparer.Ordinal));
        var catalog = DeclarationCatalog.Create(report);

        foreach (var item in expected)
        {
            var definition = DocumentDefinitions.All.Single(definition =>
                definition.Document.Header.Gid.Value == item.Document);
            var describe = Descendants(definition.Document.Content)
                .OfType<DocumentBlock.Describe>()
                .Single(node => node.Id.Value == item.Id);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);

            Assert.Equal(item.Kind, describe.Kind);
            Assert.Equal(item.Provenance, describe.ProvenanceKind);
            Assert.Equal(item.Reference, describe.LiteratureReference?.Value);
            Assert.Equal(item.Declaration, lean.Value.Value);
            var resolved = catalog.Resolve(DeclarationHandle.Create(item.Declaration));
            Assert.Equal(item.FormalKind, resolved.FormalKind);
            Assert.True(resolved.IsSorryFree);
        }
    }

    [Fact]
    public void O6LoadBearingDocumentsCarryExactStatementsAndDiligentProvenance()
    {
        (string Document, string Id, DescribeKind Kind, string Declaration,
            string? Reference)[] expected =
        [
            ("D5/S3/Weil/CriticalLine", "half-density-unitarity-characterizes-the-critical-line",
                DescribeKind.Theorem,
                "D5/S3/Weil/CriticalLine.unitarity_line_iff", null),
            ("D5/S3/Weil/EulerProduct", "finite-euler-windows-have-only-the-local-lattice",
                DescribeKind.Theorem,
                "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus",
                "D5/L/apostol1976introduction"),
            ("D5/S3/Weil/EulerProduct", "single-address-reading-is-the-von-mangoldt-weight",
                DescribeKind.Definition,
                "D5/S3/Weil/EulerProduct.single_address_reading_spec",
                "D5/L/apostol1976introduction"),
            ("D5/S3/Weil/EulerProduct", "the-logarithmic-derivative-is-the-single-address-heat-trace",
                DescribeKind.Proposition,
                "D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative",
                "D5/L/apostol1976introduction"),
        ];

        foreach (var item in expected)
        {
            var definition = DocumentDefinitions.All.Single(definition =>
                definition.Document.Header.Gid.Value == item.Document);
            var describe = Descendants(definition.Document.Content)
                .OfType<DocumentBlock.Describe>()
                .Single(node => node.Id.Value == item.Id);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);

            Assert.Equal(item.Kind, describe.Kind);
            if (item.Reference is null)
                DocumentFactAssertions.RepoDerived(describe);
            else
                DocumentFactAssertions.LiteratureAttested(describe, item.Reference!);
            Assert.Equal(item.Declaration, lean.Value.Value);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        }
    }

    [Fact]
    public void ZeroGeometryDocumentCarriesExactStatementsAndDiligentProvenance()
    {
        (string Declaration, DescribeKind Kind, LeanDeclarationKind LeanKind)[] expected =
        [
            ("D5/S3/Zeros/ZeroGeometry.projection_zero_labeled_vector_spec",
                DescribeKind.Theorem, LeanDeclarationKind.Theorem),
            ("D5/S3/Zeros/ZeroGeometry.off_line_scaling_entry_spec",
                DescribeKind.Theorem, LeanDeclarationKind.Theorem),
            ("D5/S3/Zeros/ZeroGeometry.global_factor_clearing_forces_critical_line",
                DescribeKind.Theorem, LeanDeclarationKind.Theorem),
            ("D5/S3/Zeros/ZeroGeometry.zero_quartet_scaling_spec",
                DescribeKind.Theorem, LeanDeclarationKind.Theorem),
            ("D5/S3/Zeros/ZeroGeometry.mirror_pair_distinct_iff_off_line_and_cancels",
                DescribeKind.Theorem, LeanDeclarationKind.Theorem),
            ("D5/S3/Zeros/ZeroGeometry.IsOntologicalZero",
                DescribeKind.Definition, LeanDeclarationKind.Definition),
            ("D5/S3/Zeros/ZeroGeometry.ontological_zero_re_eq_critical",
                DescribeKind.Theorem, LeanDeclarationKind.Theorem),
        ];
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Zeros/ZeroGeometry");
        var nodes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        Assert.Equal(7, nodes.Count);
        foreach (var item in expected)
        {
            var node = nodes[item.Declaration];
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);

            Assert.Equal(item.Kind, node.Kind);
            DocumentFactAssertions.RepoDerived(node);
            Assert.Null(node.LiteratureReference);
            Assert.Equal(item.Declaration, lean.Value.Value);
            DocumentFactAssertions.Declaration(node, item.LeanKind);
        }
    }

    [Fact]
    public void QuantumSkeletonDocumentCarriesExactStatementsAndDiligentProvenance()
    {
        (string Declaration, string Reference)[] expected =
        [
            ("D5/S3/Quantum/FiniteDimensional.qubit_weyl_star",
                "D5/L/schwinger1960unitary"),
            ("D5/S3/Quantum/FiniteDimensional.qubit_matrix_algebra_has_no_character",
                "D5/L/murphy1990calgebras"),
            ("D5/S3/Quantum/FiniteDimensional.born_probability_skeleton",
                "D5/L/gleason1957measures"),
        ];
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Quantum/FiniteDimensional");
        var nodes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        Assert.Equal(3, nodes.Count);
        foreach (var item in expected)
        {
            var node = nodes[item.Declaration];
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);

            Assert.Equal(DescribeKind.Theorem, node.Kind);
            DocumentFactAssertions.LiteratureAttested(node, item.Reference);
            Assert.Equal(item.Declaration, lean.Value.Value);
            DocumentFactAssertions.Declaration(node, LeanDeclarationKind.Theorem);
        }
    }

    [Fact]
    public void QubitWitnessDocumentCarriesExactStatementsAndDiligentProvenance()
    {
        (string Declaration, string? Reference)[] expected =
        [
            ("D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector",
                "D5/L/schwinger1960unitary"),
            ("D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product", null),
            ("D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate",
                "D5/L/zurek2003decoherence"),
        ];
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Quantum/QubitWitnesses");
        var nodes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        Assert.Equal(3, nodes.Count);
        foreach (var item in expected)
        {
            var node = nodes[item.Declaration];
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);

            Assert.Equal(DescribeKind.Theorem, node.Kind);
            if (item.Reference is null)
                DocumentFactAssertions.RepoDerived(node);
            else
                DocumentFactAssertions.LiteratureAttested(node, item.Reference!);
            Assert.Equal(item.Declaration, lean.Value.Value);
            DocumentFactAssertions.Declaration(node, LeanDeclarationKind.Theorem);
        }
    }

    private static IReadOnlyDictionary<string, LiteratureCitation> RepositoryCitations() =>
        LibraryNoteCatalog.Load(RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound).Root.FullPath).Citations;

    private static IEnumerable<DocumentBlock> Descendants(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (nested is null) continue;
            foreach (var descendant in Descendants(nested)) yield return descendant;
        }
    }

    private sealed class MismatchedDefinition : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => DocumentDefinition.Create(
            ScribeDocument.Create(
                DefinitionDsl.Header("D5/S1/Phase/Basic", "Mismatch fixture."),
                DefinitionDsl.H("Mismatch"),
                DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("fixture")))));
    }
}
