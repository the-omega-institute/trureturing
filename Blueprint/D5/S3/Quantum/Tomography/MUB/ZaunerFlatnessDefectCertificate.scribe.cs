using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class ZaunerFlatnessDefectCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural zeros give positive flatness-defect margins for canonical Zauner completions.",
        H("Zauner Flatness Defect Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zauner-defect-zero-entry-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate."
                    + "target_sq_le_entrywise_flatness_defect_of_zero_entry"),
                H("A zero entry bounds the defect below"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a complex matrix on finite row and column types and a real target, "
                    + "one zero entry makes the sum of squared differences between entry "
                    + "squared norms and the target at least the square of the target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zauner-defect-nonzero-target-positivity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate."
                    + "entrywise_flatness_defect_pos_of_zero_entry"),
                H("A nonzero target gives positive defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a complex matrix on finite row and column types, a nonzero real "
                    + "target and one zero entry make the sum of squared differences between "
                    + "entry squared norms and the target strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zauner-defect-normalized-margin"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate."
                    + "zaunerCanonicalCompletion_normalized_defect_ge_one_div_thirty_six"),
                H("The normalized defect is at least one thirty-sixth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let F be a three-by-three complex matrix with F times its adjoint equal "
                    + "to the identity, and let x and x-prime be arbitrary complex triples. "
                    + "For one half of the product of the Zauner left factor for x with the "
                    + "adjoint of the left factor for x-prime, the sum of squared differences "
                    + "between entry squared norms and one-sixth is at least one thirty-sixth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zauner-defect-normalized-flatness-exclusion"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate."
                    + "zaunerCanonicalCompletion_normalized_not_flat"),
                H("The normalized transition cannot be flat"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a three-by-three complex F with F times its adjoint equal to the "
                    + "identity and arbitrary complex triples x and x-prime, one half of the "
                    + "product of their Zauner left factors, with the second factor adjointed, "
                    + "cannot have every entry squared norm equal to one-sixth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zauner-defect-joint-sos-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate."
                    + "zaunerCanonicalCompletion_exact_sos_exclusion"),
                H("A joint sum-of-squares exclusion certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a three-by-three complex F satisfying the row unitary law and "
                    + "arbitrary complex triples x and x-prime, the half-scaled Zauner "
                    + "left-factor product with the second factor adjointed has defect at "
                    + "least one thirty-sixth relative to target one-sixth, and its entry "
                    + "squared norms are not all one-sixth. Both conclusions hold together."))),
                DescribeRole.Theorem))));
}
