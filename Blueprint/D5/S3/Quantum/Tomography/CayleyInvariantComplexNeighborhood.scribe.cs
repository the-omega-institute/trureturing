using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class CayleyInvariantComplexNeighborhoodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One open pole-free complex domain works at every subdivision depth and for every fixed matrix type.",
        H("A chart-invariant complex neighborhood"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayley-common-complex-neighborhood"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayleyNeighborhood"),
                H("The common domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inequality 10 abs(Im z) < 3(1+normSq z) defines the Cayley pullback of the annulus with radii one-half and two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-common-domain-open-real-poles"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_open_real_and_poles"),
                H("Open real neighborhood with quantitative pole separation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The domain is open and contains the real axis. Both denominator squared norms exceed two-fifths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-common-domain-chart-invariance"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_chart_invariance"),
                H("The same domain survives signed reciprocal transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Negation, conjugation and guarded negative reciprocal transport preserve exactly the same domain. Reciprocal transport is used only away from zero; no depth-dependent radius shrinkage is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-common-domain-phase-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_neighborhood_phase_bounds"),
                H("Uniform phase bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every unit-prefactor Cayley phase has squared norm strictly between one-fourth and four, independently of the sign or quarter-turn chart."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-common-domain-jacobian-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_cayley_jacobian_uniform_bound"),
                H("Uniform actual complex Jacobian bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If matrix coefficients have norm at most M, each Jacobian entry has norm at most 20 d M squared. In order six with unit entries the bound is 120. Gauge fixing and outcome deletion remove rows or columns only."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-guarded-phase-chart-transition"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.cayley_phase_reciprocal_transition"),
                H("Exact signed reciprocal phase identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The negative reciprocal coordinate change is compensated by negating the phase prefactor. The coordinate must be nonzero and in the common domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cayley-holomorphy-under-all-certified-restrictions"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/CayleyInvariantComplexNeighborhood.paired_residual_holomorphic_on_every_restriction"),
                H("Holomorphy persists under every certified restriction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any family of regions contained in the common coordinate domain inherits holomorphy of the actual residual. This is restriction stability. Boolean pruning and min/max are not holomorphic maps, and Newton self-invariance requires its separate quantitative budget."))),
                DescribeRole.Theorem))));
}
