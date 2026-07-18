using System.Reflection;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DocumentDiscoveryTests
{
    private const string AlgebraicModelDocumentPath = "Blueprint/D5/S0/Carrier/AlgebraicModel.md";
    private const string ConjDocumentPath = "Blueprint/D5/S0/Carrier/Conj.md";
    private const string GoldenRatioDocumentPath = "Blueprint/D5/S0/Carrier/GoldenRatio.md";
    private const string NormDocumentPath = "Blueprint/D5/S0/Carrier/Norm.md";
    private const string RingDocumentPath = "Blueprint/D5/S0/Carrier/Ring.md";
    private const string UnitsDocumentPath = "Blueprint/D5/S0/Carrier/Units.md";
    private const string NotationDocumentPath = "Blueprint/D5/S0/Conventions/Notation.md";
    private const string WDigitsDocumentPath = "Blueprint/D5/S0/Conventions/WDigits.md";
    private const string JointCoordinatesDocumentPath = "Blueprint/D5/S1/Depth/JointCoordinates.md";
    private const string JointDepthDocumentPath = "Blueprint/D5/S1/Depth/JointDepth.md";
    private const string CarryDocumentPath = "Blueprint/D5/S1/Digit/Carry.md";
    private const string PrimeAxisAdditionDocumentPath = "Blueprint/D5/S1/Digit/PrimeAxisAddition.md";
    private const string PrimeAxisEncodingDocumentPath = "Blueprint/D5/S1/Digit/PrimeAxisEncoding.md";
    private const string PrimeAxisTableDocumentPath = "Blueprint/D5/S1/Digit/PrimeAxisTable.md";
    private const string RawDocumentPath = "Blueprint/D5/S1/Digit/Raw.md";
    private const string PhaseDocumentPath = "Blueprint/D5/S1/Phase/Basic.md";
    private const string EmbeddingDocumentPath = "Blueprint/D5/S1/Scale/Embedding.md";
    private const string FibonacciEigenDocumentPath = "Blueprint/D5/S1/Scale/FibonacciEigen.md";
    private const string LogDocumentPath = "Blueprint/D5/S1/Scale/Log.md";
    private const string MinkowskiModelSetDocumentPath = "Blueprint/D5/S1/Scale/MinkowskiModelSet.md";
    private const string DecoherenceDocumentPath = "Blueprint/D5/S3/Quantum/Decoherence.md";
    private const string FiniteDimensionalDocumentPath = "Blueprint/D5/S3/Quantum/FiniteDimensional.md";
    private const string ObserverAlgebraDocumentPath = "Blueprint/D5/S3/Quantum/ObserverAlgebra.md";
    private const string QubitWitnessesDocumentPath = "Blueprint/D5/S3/Quantum/QubitWitnesses.md";
    private const string CriticalLineDocumentPath = "Blueprint/D5/S3/Weil/CriticalLine.md";
    private const string EulerProductDocumentPath = "Blueprint/D5/S3/Weil/EulerProduct.md";
    private const string LabeledZetaDocumentPath = "Blueprint/D5/S3/Weil/LabeledZeta.md";
    private const string ReflectionLedgerDocumentPath = "Blueprint/D5/S3/Weil/ReflectionLedger.md";
    private const string SpectralDynamicsDocumentPath = "Blueprint/D5/S3/Weil/SpectralDynamics.md";
    private const string SpectralHilbertDocumentPath = "Blueprint/D5/S3/Weil/SpectralHilbert.md";
    private const string ZeroGeometryDocumentPath = "Blueprint/D5/S3/Zeros/ZeroGeometry.md";
    private const string PhaseSourcePath = "Blueprint/D5/S1/Phase/Basic.scribe.cs";

    [Fact]
    public void DiscoveryFindsEveryDefinitionInCanonicalPathOrder()
    {
        Assert.Equal(
            [
                "D5/S0/Carrier/AlgebraicModel",
                "D5/S0/Carrier/Conj",
                "D5/S0/Carrier/GoldenRatio",
                "D5/S0/Carrier/Norm",
                "D5/S0/Carrier/Ring",
                "D5/S0/Carrier/Units",
                "D5/S0/Conventions/Notation",
                "D5/S0/Conventions/WDigits",
                "D5/S1/Depth/JointCoordinates",
                "D5/S1/Depth/JointDepth",
                "D5/S1/Digit/Carry",
                "D5/S1/Digit/PrimeAxisAddition",
                "D5/S1/Digit/PrimeAxisEncoding",
                "D5/S1/Digit/PrimeAxisTable",
                "D5/S1/Digit/Raw",
                "D5/S1/Phase/Basic",
                "D5/S1/Scale/Embedding",
                "D5/S1/Scale/FibonacciEigen",
                "D5/S1/Scale/Log",
                "D5/S1/Scale/MinkowskiModelSet",
                "D5/S3/Quantum/Decoherence",
                "D5/S3/Quantum/FiniteDimensional",
                "D5/S3/Quantum/ObserverAlgebra",
                "D5/S3/Quantum/QubitWitnesses",
                "D5/S3/Weil/CriticalLine",
                "D5/S3/Weil/EulerProduct",
                "D5/S3/Weil/LabeledZeta",
                "D5/S3/Weil/ReflectionLedger",
                "D5/S3/Weil/SpectralDynamics",
                "D5/S3/Weil/SpectralHilbert",
                "D5/S3/Zeros/ZeroGeometry",
            ],
            DocumentDefinitions.All.Select(static item => item.Document.Header.Gid.Value));
        Assert.Equal(
            [
                AlgebraicModelDocumentPath,
                ConjDocumentPath,
                GoldenRatioDocumentPath,
                NormDocumentPath,
                RingDocumentPath,
                UnitsDocumentPath,
                NotationDocumentPath,
                WDigitsDocumentPath,
                JointCoordinatesDocumentPath,
                JointDepthDocumentPath,
                CarryDocumentPath,
                PrimeAxisAdditionDocumentPath,
                PrimeAxisEncodingDocumentPath,
                PrimeAxisTableDocumentPath,
                RawDocumentPath,
                PhaseDocumentPath,
                EmbeddingDocumentPath,
                FibonacciEigenDocumentPath,
                LogDocumentPath,
                MinkowskiModelSetDocumentPath,
                DecoherenceDocumentPath,
                FiniteDimensionalDocumentPath,
                ObserverAlgebraDocumentPath,
                QubitWitnessesDocumentPath,
                CriticalLineDocumentPath,
                EulerProductDocumentPath,
                LabeledZetaDocumentPath,
                ReflectionLedgerDocumentPath,
                SpectralDynamicsDocumentPath,
                SpectralHilbertDocumentPath,
                ZeroGeometryDocumentPath,
            ],
            DocumentDefinitions.All.Select(static item => item.RelativePath.Value));
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
    public void GeneratedMarkdownIsDeterministicAndMatchesTheCommittedTree()
    {
        var repositoryRoot = FindRepositoryRoot();
        var rawLeanReport = Path.Combine(
            repositoryRoot,
            ".lake",
            "build",
            "stratalint",
            "raw-lean-report.json");
        if (!File.Exists(rawLeanReport))
        {
            var error = new StringWriter();
            var exit = ScribeEmitter.Emit(
                repositoryRoot,
                check: true,
                TextWriter.Null,
                error);

            Assert.Equal(1, exit);
            Assert.Contains("inspect.sh", error.ToString(), StringComparison.Ordinal);
            return;
        }

        var report = LeanCompiledArtifactReports.InspectRepository(repositoryRoot);

        foreach (var definition in DocumentDefinitions.All)
        {
            var first = CanonicalMarkdownWriter.Write(definition.Document, report);
            var second = CanonicalMarkdownWriter.Write(definition.Document, report);
            var committed = File.ReadAllBytes(
                Path.Combine(repositoryRoot, definition.RelativePath.Value));

            Assert.Equal(first.ToArray(), second.ToArray());
            Assert.Equal(committed, first.ToArray());
        }
    }

    [Fact]
    public void DigitRawContainsATypedRepoDerivedZeckendorfExample()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Digit/Raw");
        var report = LeanReportFixture.ForDocuments([definition.Document]);

        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());

        Assert.Contains(
            "\\operatorname{Z}\\left(89\\right) + \\operatorname{Z}\\left(34\\right) = \\operatorname{Z}\\left(123\\right) = 1010000000_{W}",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "Provenance: `repo-derived`",
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
        Assert.Equal(LeanDeclarationKind.Theorem, lean.Value.ExpectedKind);
        Assert.True(lean.Value.RequireNoSorry);
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
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
        Assert.Null(describe.Provenance.LiteratureReference);
        Assert.Equal(
            "D5/S1/Digit/PrimeAxisTable.prime_axis_table_spec",
            lean.Value.Value);
        Assert.Equal(LeanDeclarationKind.Theorem, lean.Value.ExpectedKind);
        Assert.True(lean.Value.RequireNoSorry);
    }

    [Fact]
    public void SelectedResidualDocumentsCarryExactStatementsAndDiligentProvenance()
    {
        (string Document, string Id, DescribeKind Kind, string Declaration,
            DescribeProvenanceKind Provenance, string? Reference)[] expected =
        [
            ("D5/S0/Carrier/AlgebraicModel", "quadratic-quotient-conjugation-trace-and-norm",
                DescribeKind.Definition,
                "D5/S0/Carrier/AlgebraicModel.golden_algebraic_model_spec",
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/stewarttall2025algebraic"),
            ("D5/S1/Depth/JointDepth", "admissible-joint-scale-digit-phase-depth",
                DescribeKind.Definition,
                "D5/S1/Depth/JointDepth.joint_depth_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S1/Digit/PrimeAxisAddition", "prime-axis-rowwise-normalization-product",
                DescribeKind.Theorem,
                "D5/S1/Digit/PrimeAxisAddition.prime_axis_addition_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S1/Scale/MinkowskiModelSet", "minkowski-lattice-window-and-labeled-model-set",
                DescribeKind.Definition,
                "D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec",
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/baakefrankgrimm2021three"),
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
            Assert.Equal(item.Provenance, describe.Provenance.Kind);
            Assert.Equal(item.Reference, describe.Provenance.LiteratureReference?.Value);
            Assert.Equal(item.Declaration, lean.Value.Value);
            Assert.Equal(LeanDeclarationKind.Theorem, lean.Value.ExpectedKind);
            Assert.True(lean.Value.RequireNoSorry);
        }
    }

    [Fact]
    public void O6LoadBearingDocumentsCarryExactStatementsAndDiligentProvenance()
    {
        (string Document, string Id, DescribeKind Kind, string Declaration,
            DescribeProvenanceKind Provenance, string? Reference)[] expected =
        [
            ("D5/S3/Weil/CriticalLine", "half-density-unitarity-characterizes-the-critical-line",
                DescribeKind.Theorem,
                "D5/S3/Weil/CriticalLine.unitarity_line_iff",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/EulerProduct", "finite-euler-windows-have-only-the-local-lattice",
                DescribeKind.Theorem,
                "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus",
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/apostol1976introduction"),
            ("D5/S3/Weil/EulerProduct", "single-address-reading-is-the-von-mangoldt-weight",
                DescribeKind.Definition,
                "D5/S3/Weil/EulerProduct.single_address_reading_spec",
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/apostol1976introduction"),
            ("D5/S3/Weil/EulerProduct", "the-logarithmic-derivative-is-the-single-address-heat-trace",
                DescribeKind.Proposition,
                "D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative",
                DescribeProvenanceKind.LiteratureAttested,
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
            Assert.Equal(item.Provenance, describe.Provenance.Kind);
            Assert.Equal(item.Reference, describe.Provenance.LiteratureReference?.Value);
            Assert.Equal(item.Declaration, lean.Value.Value);
            Assert.Equal(LeanDeclarationKind.Theorem, lean.Value.ExpectedKind);
            Assert.True(lean.Value.RequireNoSorry);
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
            Assert.Equal(DescribeProvenanceKind.RepoDerived, node.Provenance.Kind);
            Assert.Null(node.Provenance.LiteratureReference);
            Assert.Equal(item.Declaration, lean.Value.Value);
            Assert.Equal(item.LeanKind, lean.Value.ExpectedKind);
            Assert.True(lean.Value.RequireNoSorry);
        }
    }

    [Fact]
    public void ZeroGeometryDocumentDisclosesSourceOmissionsAndTheOpenO6Bridge()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Zeros/ZeroGeometry");
        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());

        string[] requiredDisclosures =
        [
            "No analytic projection operator is defined, and no projection identity outside the Dirichlet convergence half-plane is claimed.",
            "The source's coefficient factorization, unbounded-ray clause, and rotation-invariance clause are not formalized here.",
            "The governance claim excluding an address-dependent inverse register is not part of this theorem.",
            "Cross-position cancellation does not imply local balance at either position.",
            "The closure condition is carried as the arbitrary predicate closedAt; no inhabitant is asserted.",
            "The missing implication from every projected zero to local balance is exactly the open O-6 bridge.",
        ];

        foreach (var disclosure in requiredDisclosures)
        {
            Assert.Contains(disclosure, markdown, StringComparison.Ordinal);
        }

        var zeroQuartetScaling = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .Single(static node =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement).Value.Value ==
                "D5/S3/Zeros/ZeroGeometry.zero_quartet_scaling_spec");
        var zeroDataDisclosure = Assert.IsType<Inline.Text>(
            Assert.IsType<DocumentBlock.Paragraph>(
                Assert.Single(zeroQuartetScaling.Content.Items)).Content.Items.Single()).Run.Value;

        Assert.Contains("ZeroData", zeroDataDisclosure, StringComparison.Ordinal);
        Assert.Contains("does not prove", zeroDataDisclosure, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("inhabit", zeroDataDisclosure, StringComparison.OrdinalIgnoreCase);
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
            Assert.Equal(DescribeProvenanceKind.LiteratureAttested, node.Provenance.Kind);
            Assert.Equal(item.Reference, node.Provenance.LiteratureReference?.Value);
            Assert.Equal(item.Declaration, lean.Value.Value);
            Assert.Equal(LeanDeclarationKind.Theorem, lean.Value.ExpectedKind);
            Assert.True(lean.Value.RequireNoSorry);
        }
    }

    [Fact]
    public void QuantumSkeletonDocumentExplicitlyDisclosesUnformalizedNumericalCertificates()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Quantum/FiniteDimensional");
        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());

        Assert.Contains(
            "Original numerical-certificate claim not formalized: the source atom's matrix-unit relations with exact zero certificate error.",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "Original numerical-certificate claim not formalized: the source atom's separate Born control group balance to 10^-16.",
            markdown,
            StringComparison.Ordinal);
    }

    [Fact]
    public void QubitWitnessDocumentCarriesExactStatementsAndDiligentProvenance()
    {
        (string Declaration, DescribeProvenanceKind Provenance, string? Reference)[] expected =
        [
            ("D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector",
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/schwinger1960unitary"),
            ("D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate",
                DescribeProvenanceKind.LiteratureAttested,
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
            Assert.Equal(item.Provenance, node.Provenance.Kind);
            Assert.Equal(item.Reference, node.Provenance.LiteratureReference?.Value);
            Assert.Equal(item.Declaration, lean.Value.Value);
            Assert.Equal(LeanDeclarationKind.Theorem, lean.Value.ExpectedKind);
            Assert.True(lean.Value.RequireNoSorry);
        }
    }

    [Fact]
    public void QubitWitnessDocumentAccountsForEverySourceCertificate()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Quantum/QubitWitnesses");
        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());

        Assert.Contains(
            "Original numerical-certificate claim not formalized: the source atom's full matrix-unit relations with exact zero certificate error.",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "Original numerical-certificate claims not formalized: the source atom's CHSH values 2*sqrt(2) = 2.8284 and the classical local-fiber bound 2.0.",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "Original certificate coverage: the source atom's symbolic (1/2) * c0^N coherence law and fixed one-half populations are formalized exactly; the atom supplies no fixed numeric c0 or N.",
            markdown,
            StringComparison.Ordinal);
    }

    [Fact]
    public void QuantumContinuationDocumentsDiscloseStructuresScopeAndCertificates()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);
        var observerDefinition = documents["D5/S3/Quantum/ObserverAlgebra"];
        var decoherenceDefinition = documents["D5/S3/Quantum/Decoherence"];
        var report = LeanReportFixture.ForDocuments(
            [observerDefinition.Document, decoherenceDefinition.Document]);
        var observerMarkdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(observerDefinition.Document, report).AsSpan());
        var decoherenceMarkdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(decoherenceDefinition.Document, report).AsSpan());

        Assert.Contains("including an empty type", observerMarkdown, StringComparison.Ordinal);
        Assert.Contains("explicit address i", observerMarkdown, StringComparison.Ordinal);
        Assert.Contains(
            "does not construct or identify the universal C*-crossed product",
            observerMarkdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "neither observer-algebra CAS atom contains a numerical certificate",
            observerMarkdown,
            StringComparison.Ordinal);

        Assert.Contains(
            "inhabited real interval [0,1], with zero as an explicit witness",
            decoherenceMarkdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "arbitrary complex two-by-two matrix, no positivity, trace-one, or Hermiticity premise",
            decoherenceMarkdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "Original certificate disposition: the source atoms' symbolic (1/2) * c0^N coherence law and fixed one-half populations are already formalized exactly",
            decoherenceMarkdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "no fixed numeric c0 or N",
            decoherenceMarkdown,
            StringComparison.Ordinal);
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

        throw new DirectoryNotFoundException("Could not locate the repository root.");
    }

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
