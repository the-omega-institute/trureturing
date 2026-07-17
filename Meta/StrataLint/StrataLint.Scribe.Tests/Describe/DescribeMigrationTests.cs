using System.Text.Json;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeMigrationTests
{
    [Fact]
    public void RepositoryMigrationHasFiftyThreeTypedNodesAndPreservesTwentyFourFormulaSlots()
    {
        var root = FindRepositoryRoot();
        var report = DescribeReport.Build(
            root,
            DocumentDefinitions.All.Select(static definition => definition.Document));

        Assert.Equal(53, report.NodeStats.Total);
        Assert.Equal(24, report.NodeStats.FormulaContentSlots);
        Assert.Equal(1, report.NodeStats.FormulaStatements);
        Assert.Equal(52, report.NodeStats.LeanStatements);
        Assert.Equal(7, report.NodeStats.ByKind["definition"]);
        Assert.Equal(9, report.NodeStats.ByKind["proposition"]);
        Assert.Equal(36, report.NodeStats.ByKind["theorem"]);
        Assert.Equal(1, report.NodeStats.ByKind["example"]);
        Assert.Equal(32, report.NodeStats.ByProvenance["repo-derived"]);
        Assert.Equal(21, report.NodeStats.ByProvenance["literature-attested"]);
        Assert.Equal(0, report.OpenCount);
        Assert.Empty(report.SuspectedNovel);
        Assert.Empty(report.RedFindings);
    }

    [Fact]
    public void O6LoadBearingResidualNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);

        var criticalLine = Assert.Single(
            documents["D5/S3/Weil/CriticalLine"].Document.Content.Items
                .OfType<DocumentBlock.Describe>());
        AssertRepoDerivedLeanNode(
            criticalLine,
            DescribeKind.Theorem,
            "D5/S3/Weil/CriticalLine.unitarity_line_iff");

        var eulerProduct = documents["D5/S3/Weil/EulerProduct"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        Assert.Equal(3, eulerProduct.Count);
        AssertLiteratureAttestedLeanNode(
            eulerProduct["D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus"],
            DescribeKind.Theorem,
            "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus",
            "D5/L/apostol1976introduction");
        AssertLiteratureAttestedLeanNode(
            eulerProduct["D5/S3/Weil/EulerProduct.single_address_reading_spec"],
            DescribeKind.Definition,
            "D5/S3/Weil/EulerProduct.single_address_reading_spec",
            "D5/L/apostol1976introduction");
        AssertLiteratureAttestedLeanNode(
            eulerProduct["D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative"],
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

        Assert.Equal(3, nodes.Count);
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

        Assert.Equal(3, nodes.Count);
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
    public void SpectralResidualNodesUseExactTypedStatementsAndDiligentProvenance()
    {
        var documents = DocumentDefinitions.All
            .ToDictionary(static item => item.Document.Header.Gid.Value, StringComparer.Ordinal);

        var labeled = Assert.Single(
            documents["D5/S3/Weil/LabeledZeta"].Document.Content.Items
                .OfType<DocumentBlock.Describe>());
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
            .ToArray();
        Assert.Collection(
            reflection,
            node => AssertRepoDerivedLeanNode(
                node,
                DescribeKind.Proposition,
                "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq"),
            node => AssertRepoDerivedLeanNode(
                node,
                DescribeKind.Theorem,
                "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec"));

        var spectralDynamics = documents["D5/S3/Weil/SpectralDynamics"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        Assert.Equal(5, spectralDynamics.Count);
        AssertLiteratureAttestedLeanNode(
            spectralDynamics["D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.vertical_evolution_unitary_group",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralDynamics["D5/S3/Weil/SpectralDynamics.horizontal_evolution_contraction_semigroup"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.horizontal_evolution_contraction_semigroup",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralDynamics["D5/S3/Weil/SpectralDynamics.labeled_zeta_evolution_spec"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.labeled_zeta_evolution_spec",
            "D5/L/hedenmalm1997hilbert");
        var zeroQuartetResonance =
            spectralDynamics["D5/S3/Weil/SpectralDynamics.zero_quartet_resonance_spec"];
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
            spectralDynamics["D5/S3/Weil/SpectralDynamics.critical_line_characterizations"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralDynamics.critical_line_characterizations");

        var zeroGeometry = documents["D5/S3/Weil/ZeroGeometry"].Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);
        var zeroQuartetScaling =
            zeroGeometry["D5/S3/Weil/ZeroGeometry.zero_quartet_scaling_spec"];
        AssertRepoDerivedLeanNode(
            zeroQuartetScaling,
            DescribeKind.Theorem,
            "D5/S3/Weil/ZeroGeometry.zero_quartet_scaling_spec");
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
            .ToDictionary(
                static node => Assert.IsType<DescribeStatement.LeanDeclaration>(node.Statement)
                    .Value.Value,
                StringComparer.Ordinal);

        Assert.Equal(6, spectralHilbert.Count);
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum"],
            DescribeKind.Definition,
            "D5/S3/Weil/SpectralHilbert.source_pairing_eq_tsum",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_norm_sq",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_mem_iff",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_kernel",
            "D5/L/hedenmalm1997hilbert");
        AssertLiteratureAttestedLeanNode(
            spectralHilbert["D5/S3/Weil/SpectralHilbert.labeled_zeta_inner"],
            DescribeKind.Theorem,
            "D5/S3/Weil/SpectralHilbert.labeled_zeta_inner",
            "D5/L/hedenmalm1997hilbert");
        AssertRepoDerivedLeanNode(
            spectralHilbert["D5/S3/Weil/SpectralHilbert.resonance_partner_spec"],
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
                Declaration: "D5/S0/Carrier/GoldenRatio.golden_ratio_spec",
                Reference: "D5/L/koshy2001fibonacci"),
            (
                Document: "D5/S1/Scale/FibonacciEigen",
                Declaration: "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec",
                Reference: "D5/L/koshy2001fibonacci"),
            (
                Document: "D5/S0/Carrier/AlgebraicModel",
                Declaration: "D5/S0/Carrier/AlgebraicModel.golden_algebraic_model_spec",
                Reference: "D5/L/stewarttall2025algebraic"),
            (
                Document: "D5/S1/Scale/MinkowskiModelSet",
                Declaration: "D5/S1/Scale/MinkowskiModelSet.minkowski_model_set_spec",
                Reference: "D5/L/baakefrankgrimm2021three"),
        };

        foreach (var item in expected)
        {
            var document = Assert.Single(
                DocumentDefinitions.All.Select(static definition => definition.Document),
                document => document.Header.Gid.Value == item.Document);
            var describe = Assert.Single(document.Content.Items.OfType<DocumentBlock.Describe>());
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
        Assert.Equal("DESCRIBE-NODES", document.RootElement.GetProperty("case_id").GetString());
        Assert.Equal(53, document.RootElement.GetProperty("node_stats").GetProperty("total").GetInt32());
        Assert.Equal(0, document.RootElement.GetProperty("open_count").GetInt32());
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
