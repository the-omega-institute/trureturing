using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class AdvectionClosureInstanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fourier witness violates the mixed-term condition of the quadratic closure criterion in a five-mode Galerkin state space.",
        H("Advection Closure Instance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-state"),
                DeclarationHandle.Create(Prefix + "State"),
                H("State"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Five retained complex velocity amplitudes, regarded as a real vector space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-mode"),
                DeclarationHandle.Create(Prefix + "mode"),
                H("mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The generated transverse mode followed by the original four input modes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-embed"),
                DeclarationHandle.Create(Prefix + "embed"),
                H("embed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Linear zero extension of the four input amplitudes to the five retained modes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-family"),
                DeclarationHandle.Create(Prefix + "family"),
                H("family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original two-amplitude family in the enlarged state space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-b"),
                DeclarationHandle.Create(Prefix + "B"),
                H("B"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full retained convolution followed by Leray projection, bundled bilinearly over the reals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-l"),
                DeclarationHandle.Create(Prefix + "L"),
                H("L"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The viscous Fourier multiplier on every retained mode."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-p"),
                DeclarationHandle.Create(Prefix + "P"),
                H("P"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The squared-frequency cutoff at one on the retained state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-projection-idempotent"),
                DeclarationHandle.Create(Prefix + "projection_idempotent"),
                H("projection idempotent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The low-mode cutoff is an idempotent linear projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-family-observation"),
                DeclarationHandle.Create(Prefix + "family_observation"),
                H("family observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The projected family is exactly the original complete low observation sampled at retained modes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-family-acceleration"),
                DeclarationHandle.Create(Prefix + "family_acceleration"),
                H("family acceleration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Galerkin vector field agrees with the fluid acceleration at every retained output on the family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-mixed-witness"),
                DeclarationHandle.Create(Prefix + "mixed_witness"),
                H("mixed witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A visible wave and a hidden wave have a nonzero observed mixed interaction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-hidden-linear"),
                DeclarationHandle.Create(Prefix + "hidden_linear"),
                H("hidden linear"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Viscosity preserves the kernel of the low-mode projection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-mixed-condition-fails"),
                DeclarationHandle.Create(Prefix + "mixed_condition_fails"),
                H("mixed condition fails"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The third condition of the general quadratic closure criterion fails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-no-exact-closure"),
                DeclarationHandle.Create(Prefix + "no_exact_closure"),
                H("no exact closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This concrete Galerkin instance has no exact closure, by the general quadratic criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-exact-closure-implies-fluid-predictor"),
                DeclarationHandle.Create(Prefix + "exact_closure_implies_fluid_predictor"),
                H("exact closure implies fluid predictor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any global exact vector closure would predict the original transverse fluid coefficient on the family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-fluid-gap-from-mixed"),
                DeclarationHandle.Create(Prefix + "fluid_gap_from_mixed"),
                H("fluid gap from mixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same mixed obstruction gives a fluid acceleration gap through the general observed-increment identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("advection-closure-instance-no-fluid-predictor-from-mixed"),
                DeclarationHandle.Create(Prefix + "no_fluid_predictor_from_mixed"),
                H("no fluid predictor from mixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mixed obstruction re-derives exactly the original scalar predictor impossibility on the whole family."))),
                DescribeRole.Theorem))));
}
