using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class ZaunerCompletionFibreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural zeros obstruct nonzero flat moduli for Zauner relative Grams.",
        H("Zauner Completion Fibre"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "zauner-fibre-unnormalized-zauner-left-factor"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre."
                    + "zaunerLeftFactor"),
                H("Unnormalized Zauner left factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a complex square matrix F and row weights x, the matrix on Fin 2 "
                    + "times the coordinate type has blocks F, xF, F, and minus xF, where xF "
                    + "multiplies each row of F by its weight."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "zauner-fibre-upper-right-cross-block-vanishes"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre."
                    + "zaunerLeftFactor_crossGram_upperRight_zero"),
                H("Upper-right cross block vanishes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite Fourier coordinate type, any common block F, and any "
                    + "two row-weight families, the upper-right block of the adjoint of the "
                    + "first Zauner left factor times the second is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "zauner-fibre-lower-left-cross-block-vanishes"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre."
                    + "zaunerLeftFactor_crossGram_lowerLeft_zero"),
                H("Lower-left cross block vanishes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite Fourier coordinate type, any common block F, and any "
                    + "two row-weight families, the lower-left block of the adjoint of the "
                    + "first Zauner left factor times the second is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "zauner-fibre-factor-relative-flatness-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre."
                    + "zaunerLeftFactor_crossGram_not_nonzero_flat"),
                H("Factor-relative flatness obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty finite coordinate type, the relative Gram of two Zauner "
                    + "left factors with the same block F cannot have every entry of squared "
                    + "norm equal to a prescribed nonzero real number."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "zauner-fibre-distinct-completion-modes-decouple"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre."
                    + "zaunerLeftFactor_mul_conjTranspose_offMode_zero"),
                H("Distinct completion modes decouple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If F times its adjoint is the identity, the first Zauner left factor "
                    + "times the adjoint of a second with the same F has zero entries between "
                    + "distinct Fourier coordinates, for either choice of block rows and "
                    + "arbitrary row-weight families."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "zauner-fibre-canonical-completion-flatness-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre."
                    + "zaunerCanonicalCompletion_crossGram_not_nonzero_flat"),
                H("Canonical completion flatness obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a three-by-three F with row Gram equal to the identity and any two "
                    + "row-weight families, the first Zauner left factor times the adjoint of "
                    + "the second cannot have every entry of squared norm equal to a "
                    + "prescribed nonzero real number."))),
                DescribeRole.Theorem))));
}
