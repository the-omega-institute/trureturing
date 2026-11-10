using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums.Fermat;

internal sealed class JacobiNormLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CharacterSums/Fermat/JacobiNormLift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative Jacobi sums lift through finite-field norm and trace pullback.",
        H("Jacobi Sums under Finite-Field Norm Lift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fermat-negative-jacobi-norm-lift"),
                DeclarationHandle.Create(Prefix + "neg_jacobiSum_norm_lift"),
                H("Negative Jacobi norm lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite fields k and K with an algebra structure k → K, complex multiplicative "
                        + "characters chi and phi on k, and a complex additive character psi on k, assume psi "
                        + "is nontrivial and chi * phi is nontrivial. Writing N for the finite-field norm, Tr "
                        + "for the finite-field trace, and r = Module.finrank k K, the checked theorem states "
                        + "-J_K(chi ∘ N, phi ∘ N) = (-J_k(chi, phi))^r.")),
                    Paragraph(Text(
                        "The proof combines the existing Langlands-normalized Hasse–Davenport lift with the "
                        + "Jacobi–Gauss quotient identity. Norm pullback preserves the product-character "
                        + "nontriviality hypothesis. The minus sign records the ordinary Jacobi-sum parity "
                        + "factor and gives a formula uniform in the extension degree.")),
                    Paragraph(Text(
                        "This is the extension-compatibility interface for the existing single-field Fermat "
                        + "point-count development. The extension-field point-count family and its zeta "
                        + "factorization remain subsequent targets."))),
                DescribeRole.Theorem))));
}
