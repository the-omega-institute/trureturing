using System.Text.Json;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeMigrationTests
{
    [Fact]
    public void InventoryCurrentDescribeKindContracts()
    {
        var inventory = DocumentDefinitions.All
            .SelectMany(static definition => EnumerateDescribe(definition.Document.Content)
                .Select(node => new
                {
                    Document = definition.Document.Header.Gid.Value,
                    Node = node,
                }))
            .ToArray();
        var ownershipViolations = inventory
            .Where(static item => item.Node.Statement is DescribeStatement.LeanDeclaration)
            .Where(item => !AssertSameModule(
                item.Document,
                ((DescribeStatement.LeanDeclaration)item.Node.Statement).Value.Value))
            .Select(static item => $"{item.Document}#{item.Node.Id.Value}")
            .ToArray();

        Assert.NotEmpty(DocumentDefinitions.All);
        Assert.Equal(
            DocumentDefinitions.All.Length,
            DocumentDefinitions.All.Select(static item => item.SourcePath).Distinct().Count());
        Assert.NotEmpty(inventory);
        Assert.All(inventory, static item => AssertDescribeContract(item.Node));
        Assert.Equal(
        [
            "D5/S0/Carrier/Norm#golden-norm-is-power-multiplicative",
            "D5/S0/Carrier/Norm#norm-euclidean-division",
            "D5/S0/Carrier/Norm#principal-ideal-domain",
        ],
            ownershipViolations.Order(StringComparer.Ordinal));
    }

    private static void AssertDescribeContract(DocumentBlock.Describe node)
    {
        switch (node.Kind)
        {
            case DescribeKind.Definition:
                Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);
                break;
            case DescribeKind.Theorem:
            case DescribeKind.Proposition:
            case DescribeKind.Lemma:
                Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);
                Assert.NotNull(node.StatementFormula);
                break;
            case DescribeKind.Example:
                Assert.IsType<DescribeStatement.FormulaAst>(node.Statement);
                Assert.Null(node.StatementFormula);
                break;
            case DescribeKind.Remark:
                Assert.True(
                    node.Statement is DescribeStatement.FormulaAst or DescribeStatement.LeanDeclaration,
                    $"Remark {node.Id.Value} must use a typed formula or Lean statement.");
                Assert.Null(node.StatementFormula);
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(node.Kind));
        }

        Assert.NotEqual(DescribeProvenanceKind.Unassessed, node.Provenance.Kind);
        if (node.Provenance.Kind == DescribeProvenanceKind.LiteratureAttested)
        {
            Assert.NotNull(node.Provenance.LiteratureReference);
        }
        else
        {
            Assert.Null(node.Provenance.LiteratureReference);
        }
    }

    private static bool AssertSameModule(string documentGid, string declarationGid)
    {
        var separator = declarationGid.LastIndexOf('.');
        return separator > 0
            && string.Equals(documentGid, declarationGid[..separator], StringComparison.Ordinal);
    }

    [Fact]
    public void EveryCurrentTheoremClassNodeHasAnExplicitLatexStatement()
    {
        var nodes = DocumentDefinitions.All
            .SelectMany(static definition => EnumerateDescribe(definition.Document.Content))
            .Where(static node => node.Kind is
                DescribeKind.Theorem or DescribeKind.Proposition or DescribeKind.Lemma)
            .ToArray();

        Assert.NotEmpty(nodes);
        Assert.All(nodes, static node => Assert.NotNull(node.StatementFormula));
    }

    [Fact]
    public void RepositoryReportMatchesAnIndependentAstInventory()
    {
        var root = FindRepositoryRoot();
        var expected = DeriveContentInventory();
        var report = DescribeReport.Build(
            root,
            DocumentDefinitions.All.Select(static definition => definition.Document));

        Assert.Equal(expected.Total, report.NodeStats.Total);
        Assert.Equal(expected.FormulaContentSlots, report.NodeStats.FormulaContentSlots);
        Assert.Equal(expected.FormulaStatements, report.NodeStats.FormulaStatements);
        Assert.Equal(expected.LeanStatements, report.NodeStats.LeanStatements);
        Assert.Equal(expected.ByKind, report.NodeStats.ByKind);
        Assert.Equal(expected.ByProvenance, report.NodeStats.ByProvenance);
        Assert.Equal(expected.Unassessed, report.OpenCount);
        Assert.Equal(expected.SuspectedNovel, report.SuspectedNovel.Length);
        Assert.Empty(report.SuspectedNovel);
        Assert.Empty(report.RedFindings);
    }

    private static IEnumerable<DocumentBlock.Describe> EnumerateDescribe(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            switch (block)
            {
                case DocumentBlock.Section section:
                    foreach (var nested in EnumerateDescribe(section.Content))
                    {
                        yield return nested;
                    }
                    break;
                case DocumentBlock.Describe describe:
                    yield return describe;
                    foreach (var nested in EnumerateDescribe(describe.Content))
                    {
                        yield return nested;
                    }
                    break;
            }
        }
    }

    [Fact]
    public void RemarkBatchNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        (string Document, string Id, string Declaration,
            DescribeProvenanceKind Provenance, string? Reference)[] expected =
        [
            ("D5/S1/Scale/MinkowskiModelSet", "value-and-code-geometries",
                "D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec",
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/baakefrankgrimm2021three"),
            ("D5/S3/Weil/CriticalLine", "unitary-weight-is-not-a-zero-proof",
                "D5/S3/Weil/CriticalLine.unitarity_line_iff",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/EulerProduct", "journal-and-ledger-readings",
                "D5/S3/Weil/EulerProduct.single_address_reading_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/EulerProduct", "finite-euler-windows-do-not-create-global-zeros",
                "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/ReflectionLedger", "symmetry-channel-is-not-location-force",
                "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/ReflectionLedger", "symmetry-does-not-force-fixed-points",
                "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/ReflectionLedger", "fixed-line-versus-orbit-collapse",
                "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/ReflectionLedger", "set-invariance-versus-pointwise-invariance",
                "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/ReflectionLedger", "antilinear-reflection-produces-a-line",
                "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/ReflectionLedger", "invariant-set-need-not-lie-in-fixed-locus",
                "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/ReflectionLedger", "scaled-midline-reading",
                "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralDynamics", "diagonal-flow-and-generator-boundary",
                "D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralDynamics", "two-regimes-and-two-directions",
                "D5/S3/Weil/SpectralDynamics.critical_line_characterizations",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralDynamics", "phase-delay-is-not-address-delay",
                "D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralDynamics", "off-line-pairs-remain-conditional",
                "D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralDynamics", "counting-does-not-locate-real-parts",
                "D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralDynamics", "equalities-do-not-supply-positivity",
                "D5/S3/Weil/SpectralDynamics.critical_line_characterizations",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralDynamics", "speculative-off-line-effects-are-not-formalized",
                "D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec",
                DescribeProvenanceKind.RepoDerived, null),
            ("D5/S3/Weil/SpectralHilbert", "hardy-space-identification",
                "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner",
                DescribeProvenanceKind.LiteratureAttested,
                "D5/L/hedenmalm1997hilbert"),
        ];

        (string Document, string Id)[] formulaExpected =
        [
            ("D5/S0/Carrier/Norm", "two-square-norm-as-a-shared-interpretive-core"),
            ("D5/S1/Phase/Basic", "visible-phase-and-hidden-prime-fiber"),
            ("D5/S1/Phase/Basic", "congruence-readings-close-under-dual-completion"),
            ("D5/S1/Phase/Basic", "the-two-phase-duality-loops"),
            ("D5/S1/Phase/Basic", "dense-phase-leaves-and-discrete-switching"),
            ("D5/S1/Scale/MinkowskiModelSet", "off-diagonal-load-and-diagonal-blindness"),
            ("D5/S1/Scale/MinkowskiModelSet", "scaled-zero-images-need-an-independent-engine"),
            ("D5/S1/Scale/MinkowskiModelSet", "the-continuation-wall-is-a-transported-boundary"),
            ("D5/S3/Weil/ReflectionLedger", "three-order-two-mechanisms-have-different-sources"),
            ("D5/S3/Weil/SpectralDynamics", "thermal-time-is-a-meta-time-not-a-physical-history"),
            ("D5/S3/Weil/SpectralDynamics", "causal-direction-requires-irreversible-bookkeeping"),
        ];

        var actual = DocumentDefinitions.All
            .SelectMany(static definition => definition.Document.Content.Items
                .OfType<DocumentBlock.Describe>()
                .Where(static node => node.Kind == DescribeKind.Remark)
                .Select(node => new
                {
                    Document = definition.Document.Header.Gid.Value,
                    Node = node,
                }))
            .ToDictionary(
                static item => $"{item.Document}#{item.Node.Id.Value}",
                StringComparer.Ordinal);

        foreach (var item in expected)
        {
            var node = actual[$"{item.Document}#{item.Id}"].Node;
            var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);

            Assert.Equal(item.Declaration, statement.Value.Value);
            Assert.Equal(LeanDeclarationKind.Theorem, statement.Value.ExpectedKind);
            Assert.True(statement.Value.RequireNoSorry);
            Assert.Equal(item.Provenance, node.Provenance.Kind);
            Assert.Equal(item.Reference, node.Provenance.LiteratureReference?.Value);
        }

        foreach (var item in formulaExpected)
        {
            var node = actual[$"{item.Document}#{item.Id}"].Node;

            Assert.IsType<DescribeStatement.FormulaAst>(node.Statement);
            Assert.Equal(DescribeProvenanceKind.RepoDerived, node.Provenance.Kind);
            Assert.Null(node.Provenance.LiteratureReference);
        }
    }

    [Fact]
    public void O6LoadBearingResidualNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);

        var criticalLine = Assert.Single(
            documents["D5/S3/Weil/CriticalLine"].Document.Content.Items
                .OfType<DocumentBlock.Describe>(),
            node => node.Id.Value == "half-density-unitarity-characterizes-the-critical-line");
        AssertRepoDerivedLeanNode(
            criticalLine,
            DescribeKind.Theorem,
            "D5/S3/Weil/CriticalLine.unitarity_line_iff");

        var eulerProduct = documents["D5/S3/Weil/EulerProduct"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(static node => node.Id.Value, StringComparer.Ordinal);

        AssertLiteratureAttestedLeanNode(
            eulerProduct["finite-euler-windows-have-only-the-local-lattice"],
            DescribeKind.Theorem,
            "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus",
            "D5/L/apostol1976introduction");
        AssertLiteratureAttestedLeanNode(
            eulerProduct["single-address-reading-is-the-von-mangoldt-weight"],
            DescribeKind.Definition,
            "D5/S3/Weil/EulerProduct.single_address_reading_spec",
            "D5/L/apostol1976introduction");
        AssertLiteratureAttestedLeanNode(
            eulerProduct["the-logarithmic-derivative-is-the-single-address-heat-trace"],
            DescribeKind.Proposition,
            "D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative",
            "D5/L/apostol1976introduction");
    }

    [Fact]
    public void QuantumSkeletonNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);
        var nodes = documents["D5/S3/Quantum/FiniteDimensional"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        AssertLiteratureAttestedLeanNode(
            nodes["D5/S3/Quantum/FiniteDimensional.qubit_weyl_star"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/FiniteDimensional.qubit_weyl_star",
            "D5/L/schwinger1960unitary");
        AssertLiteratureAttestedLeanNode(
            nodes["D5/S3/Quantum/FiniteDimensional.qubit_matrix_algebra_has_no_character"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/FiniteDimensional.qubit_matrix_algebra_has_no_character",
            "D5/L/murphy1990calgebras");
        AssertLiteratureAttestedLeanNode(
            nodes["D5/S3/Quantum/FiniteDimensional.born_probability_skeleton"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/FiniteDimensional.born_probability_skeleton",
            "D5/L/gleason1957measures");
    }

    [Fact]
    public void QubitWitnessNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);
        var nodes = documents["D5/S3/Quantum/QubitWitnesses"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        AssertLiteratureAttestedLeanNode(
            nodes["D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector",
            "D5/L/schwinger1960unitary");
        AssertRepoDerivedLeanNode(
            nodes["D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product");
        AssertLiteratureAttestedLeanNode(
            nodes["D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate",
            "D5/L/zurek2003decoherence");
    }

    [Fact]
    public void QuantumContinuationNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);
        var observer = documents["D5/S3/Quantum/ObserverAlgebra"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);
        var decoherence = documents["D5/S3/Quantum/Decoherence"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        AssertLiteratureAttestedLeanNode(
            observer["D5/S3/Quantum/ObserverAlgebra.observer_update_covariant_group_skeleton"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/ObserverAlgebra.observer_update_covariant_group_skeleton",
            "D5/L/schwinger1960unitary");
        AssertLiteratureAttestedLeanNode(
            observer["D5/S3/Quantum/ObserverAlgebra.observer_read_update_noncommutative"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/ObserverAlgebra.observer_read_update_noncommutative",
            "D5/L/schwinger1960unitary");

        AssertLiteratureAttestedLeanNode(
            decoherence["D5/S3/Quantum/Decoherence.phase_damping_composition"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/Decoherence.phase_damping_composition",
            "D5/L/zurek2003decoherence");
        AssertLiteratureAttestedLeanNode(
            decoherence["D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal"],
            DescribeKind.Theorem,
            "D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal",
            "D5/L/zurek2003decoherence");
    }

    [Fact]
    public void SpectralResidualNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);

        var labeled = Assert.Single(
            documents["D5/S3/Weil/LabeledZeta"].Document.Content.Items
                .OfType<DocumentBlock.Describe>(),
            static node => node.Id.Value == "labeled-zeta-vector-never-vanishes");
        var labeledStatement = Assert.IsType<DescribeStatement.LeanDeclaration>(labeled.Statement);
        Assert.Equal(
            "D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero",
            labeledStatement.Value.Value);
        Assert.Equal(DescribeKind.Theorem, labeled.Kind);
        Assert.Equal(DescribeProvenanceKind.LiteratureAttested, labeled.Provenance.Kind);
        Assert.Equal(
            "D5/L/hedenmalm1997hilbert",
            labeled.Provenance.LiteratureReference?.Value);

        var reflection = documents["D5/S3/Weil/ReflectionLedger"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(static node => node.Id.Value, StringComparer.Ordinal);
        AssertRepoDerivedLeanNode(
            reflection["mirror-fixed-points-lie-on-the-critical-line"],
            DescribeKind.Proposition,
            "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq");
        AssertRepoDerivedLeanNode(
            reflection["mirror-reverses-every-scaling-entry"],
            DescribeKind.Theorem,
            "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec");

        var spectralDynamics = documents["D5/S3/Weil/SpectralDynamics"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(static node => node.Id.Value, StringComparer.Ordinal);

        AssertLiteratureAttestedLeanNode(
            spectralDynamics["vertical-evolution-is-a-norm-preserving-group"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralDynamics["forward-horizontal-evolution-is-a-contraction-semigroup"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.horizontal_evolution_contraction_semigroup",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralDynamics["labeled-zeta-vectors-follow-the-coordinate-evolutions"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.labeled_zeta_evolution_spec",
            "D5/L/hedenmalm1997hilbert");
        var zeroQuartetResonance =
            spectralDynamics["zero-symmetries-form-the-kernel-resonant-cross-pairs"];
        AssertRepoDerivedLeanNode(
            zeroQuartetResonance,
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec");
        var zeroQuartetDisclosure = Assert.IsType<Inline.Text>(
            Assert.IsType<DocumentBlock.Paragraph>(
                Assert.Single(zeroQuartetResonance.Content.Items)).Content.Items.Single()).Run.Value;
        Assert.Contains(
            "conditional on a supplied ZeroData value",
            zeroQuartetDisclosure,
            StringComparison.Ordinal);
        Assert.Contains(
            "does not prove that ZeroData is inhabited",
            zeroQuartetDisclosure,
            StringComparison.Ordinal);
        AssertRepoDerivedLeanNode(
            spectralDynamics["critical-line-predicates-use-one-abscissa"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.critical_line_characterizations");

        var zeroGeometry = documents["D5/S3/Zeros/ZeroGeometry"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);
        var zeroQuartetScaling =
            zeroGeometry["D5/S3/Zeros/ZeroGeometry.zero_quartet_scaling_spec"];
        AssertRepoDerivedLeanNode(
            zeroQuartetScaling,
            DescribeKind.Theorem,
            "D5/S3/Zeros/ZeroGeometry.zero_quartet_scaling_spec");
        var zeroQuartetScalingDisclosure = Assert.IsType<Inline.Text>(
            Assert.IsType<DocumentBlock.Paragraph>(
                Assert.Single(zeroQuartetScaling.Content.Items)).Content.Items.Single()).Run.Value;
        Assert.Contains(
            "zero_conjugation and zero_reflection fields are premises",
            zeroQuartetScalingDisclosure,
            StringComparison.Ordinal);
        Assert.Contains(
            "does not prove that ZeroData is inhabited: no instance or example exists",
            zeroQuartetScalingDisclosure,
            StringComparison.Ordinal);
        Assert.Contains(
            "their multiplicity-preservation laws",
            zeroQuartetScalingDisclosure,
            StringComparison.Ordinal);
        Assert.Contains(
            "does not close the source theorem",
            zeroQuartetScalingDisclosure,
            StringComparison.Ordinal);

        var spectralHilbert = documents["D5/S3/Weil/SpectralHilbert"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(static node => node.Id.Value, StringComparer.Ordinal);

        AssertLiteratureAttestedLeanNode(
            spectralHilbert["source-pairing-completes-the-coefficient-space"],
            DescribeKind.Definition,
            "D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["labeled-zeta-norm-is-zeta-on-the-convergence-side"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["labeled-zeta-membership-has-the-half-density-boundary"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["coefficient-pairing-is-the-zeta-kernel"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["hilbert-pairing-is-the-zeta-kernel"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner",
            "D5/L/hedenmalm1997hilbert");
        AssertRepoDerivedLeanNode(
            spectralHilbert["mirror-is-the-unique-resonance-partner"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.resonance_partner_spec");
    }

    [Fact]
    public void ResidualPilotNodesUseTypedLeanStatementsAndDiligentLiteratureProvenance()
    {
        var expected = new[]
        {
            (
                Document: "D5/S0/Carrier/GoldenRatio",
                Id: "radical-fixed-point-and-conjugate-identities",
                Declaration: "D5/S0/Carrier/GoldenRatio.golden_ratio_spec",
                Reference: "D5/L/koshy2001fibonacci"),
            (
                Document: "D5/S1/Scale/FibonacciEigen",
                Id: "golden-eigenpairs-and-contracting-error",
                Declaration: "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec",
                Reference: "D5/L/koshy2001fibonacci"),
            (
                Document: "D5/S0/Carrier/AlgebraicModel",
                Id: "quadratic-quotient-conjugation-trace-and-norm",
                Declaration: "D5/S0/Carrier/AlgebraicModel.golden_algebraic_model_spec",
                Reference: "D5/L/stewarttall2025algebraic"),
            (
                Document: "D5/S0/Carrier/Norm",
                Id: "norm-euclidean-division",
                Declaration: "D5/S0/Carrier/Euclidean.golden_division",
                Reference: "D5/L/Carrier/chatland1949euclidean"),
            (
                Document: "D5/S1/Scale/MinkowskiModelSet",
                Id: "minkowski-lattice-window-and-labeled-model-set",
                Declaration: "D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec",
                Reference: "D5/L/baakefrankgrimm2021three"),
        };

        foreach (var item in expected)
        {
            var document = Assert.Single(
                DocumentDefinitions.All.Select(static definition => definition.Document),
                document => document.Header.Gid.Value == item.Document);
            var describe = Assert.Single(
                document.Content.Items.OfType<DocumentBlock.Describe>(),
                node => node.Id.Value == item.Id);
            var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);

            Assert.Equal(item.Declaration, statement.Value.Value);
            Assert.Equal(DescribeProvenanceKind.LiteratureAttested, describe.Provenance.Kind);
            Assert.Equal(item.Reference, describe.Provenance.LiteratureReference?.Value);
        }
    }

    [Fact]
    public void LegacyNarrativeNodeTypesAreAbsentAfterTheSingleStepMigration()
    {
        var nestedNames = typeof(DocumentBlock).GetNestedTypes()
            .Select(static type => type.Name)
            .ToHashSet(StringComparer.Ordinal);

        Assert.DoesNotContain("Proposition", nestedNames);
        Assert.DoesNotContain("Theorem", nestedNames);
        Assert.DoesNotContain("ComputedValue", nestedNames);
        Assert.DoesNotContain("RenderedStatement", nestedNames);
    }

    [Fact]
    public void DescribeReportVerbReturnsTheMachineQueryableLedger()
    {
        var output = new StringWriter();
        var error = new StringWriter();

        var exit = ScribeCli.Run(
            ["describe-report", "--json"],
            FindRepositoryRoot(),
            output,
            error,
            LeanReportFixture.ForDocuments(
                DocumentDefinitions.All.Select(static definition => definition.Document)));

        Assert.Equal(0, exit);
        Assert.Equal(string.Empty, error.ToString());
        using var document = JsonDocument.Parse(output.ToString());
        var expected = DeriveContentInventory();
        Assert.Equal("DESCRIBE-NODES", document.RootElement.GetProperty("case_id").GetString());
        Assert.Equal(
            expected.Total,
            document.RootElement.GetProperty("node_stats").GetProperty("total").GetInt32());
        Assert.Equal(expected.Unassessed, document.RootElement.GetProperty("open_count").GetInt32());
    }

    [Fact]
    public void QuantitativeAndIdentityUpgradeCandidatesAreNotDescribeRemarks()
    {
        var forbidden = new HashSet<string>(StringComparer.Ordinal)
        {
            "D5/S1/Scale/MinkowskiModelSet#trace-map-program-and-missing-hyperbolicity-engine",
            "D5/S1/Scale/MinkowskiModelSet#window-parity-becomes-a-congruence-pattern",
            "D5/S1/Phase/Basic#poisson-summation-is-the-cofinal-analytic-limit",
            "D5/S1/Phase/Basic#quasiperiodic-return-is-not-exact-recurrence",
            "D5/S3/Weil/EulerProduct#sum-and-product-are-two-views-of-zeta",
            "D5/S3/Weil/EulerProduct#the-pole-is-not-an-off-line-zero",
            "D5/S3/Weil/SpectralHilbert#bridge-distributions-do-not-settle-pointwise-zeros",
            "D5/S3/Weil/SpectralDynamics#inequalities-carry-the-narrative-arrow-of-time",
            "D5/S3/Weil/SpectralDynamics#riemann-hypothesis-shaped-real-zero-properties-form-a-family",
        };
        var actual = DocumentDefinitions.All
            .SelectMany(static definition => definition.Document.Content.Items
                .OfType<DocumentBlock.Describe>()
                .Select(node => $"{definition.Document.Header.Gid.Value}#{node.Id.Value}"))
            .ToHashSet(StringComparer.Ordinal);

        Assert.Empty(forbidden.Intersect(actual));
    }

    private static void AssertRepoDerivedLeanNode(
        DocumentBlock.Describe node,
        DescribeKind kind,
        string declaration)
    {
        var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);

        Assert.Equal(kind, node.Kind);
        Assert.Equal(declaration, statement.Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, node.Provenance.Kind);
        Assert.Null(node.Provenance.LiteratureReference);
    }

    private static void AssertLiteratureAttestedLeanNode(
        DocumentBlock.Describe node,
        DescribeKind kind,
        string declaration,
        string reference)
    {
        var statement = Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement);

        Assert.Equal(kind, node.Kind);
        Assert.Equal(declaration, statement.Value.Value);
        Assert.Equal(DescribeProvenanceKind.LiteratureAttested, node.Provenance.Kind);
        Assert.Equal(reference, node.Provenance.LiteratureReference?.Value);
    }

    private static ContentInventory DeriveContentInventory()
    {
        var blocks = DocumentDefinitions.All
            .SelectMany(static definition => EnumerateBlocks(definition.Document.Content))
            .ToArray();
        var nodes = blocks.OfType<DocumentBlock.Describe>().ToArray();
        var byKind = new SortedDictionary<string, int>(
            nodes.GroupBy(static node => KindName(node.Kind), StringComparer.Ordinal)
                .ToDictionary(static group => group.Key, static group => group.Count()),
            StringComparer.Ordinal);
        var byProvenance = new SortedDictionary<string, int>(
            nodes.GroupBy(static node => ProvenanceName(node.Provenance.Kind), StringComparer.Ordinal)
                .ToDictionary(static group => group.Key, static group => group.Count()),
            StringComparer.Ordinal);

        return new ContentInventory(
            nodes.Length,
            blocks.OfType<DocumentBlock.DisplayFormula>().Count()
                + blocks.OfType<DocumentBlock.Paragraph>().Sum(static paragraph =>
                    paragraph.Content.Items.Count(static inline => inline is Inline.InlineFormula)),
            nodes.Count(static node => node.Statement is DescribeStatement.FormulaAst),
            nodes.Count(static node => node.Statement is DescribeStatement.LeanDeclaration),
            byKind,
            byProvenance,
            nodes.Count(static node => node.Provenance.Kind == DescribeProvenanceKind.Unassessed),
            nodes.Count(static node => node.Provenance.Kind == DescribeProvenanceKind.SuspectedNovel));
    }

    private static IEnumerable<DocumentBlock> EnumerateBlocks(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (nested is null)
            {
                continue;
            }

            foreach (var descendant in EnumerateBlocks(nested))
            {
                yield return descendant;
            }
        }
    }

    private static string KindName(DescribeKind kind) => kind switch
    {
        DescribeKind.Definition => "definition",
        DescribeKind.Theorem => "theorem",
        DescribeKind.Proposition => "proposition",
        DescribeKind.Lemma => "lemma",
        DescribeKind.Example => "example",
        DescribeKind.Remark => "remark",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };

    private static string ProvenanceName(DescribeProvenanceKind provenance) => provenance switch
    {
        DescribeProvenanceKind.LiteratureAttested => "literature-attested",
        DescribeProvenanceKind.RepoDerived => "repo-derived",
        DescribeProvenanceKind.SuspectedNovel => "suspected-novel",
        DescribeProvenanceKind.Unassessed => "unassessed",
        _ => throw new ArgumentOutOfRangeException(nameof(provenance)),
    };

    private sealed record ContentInventory(
        int Total,
        int FormulaContentSlots,
        int FormulaStatements,
        int LeanStatements,
        IReadOnlyDictionary<string, int> ByKind,
        IReadOnlyDictionary<string, int> ByProvenance,
        int Unassessed,
        int SuspectedNovel);

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

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
