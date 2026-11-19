using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class GeneralDirichletGaussNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fourier inversion extends the primitive Dirichlet Gauss norm identity from prime moduli to every nonzero modulus.",
        H("General primitive Dirichlet Gauss norm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primitive-gauss-product-fourier"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_gauss_product_fourier"),
                H("Primitive Gauss product by finite Fourier inversion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a primitive complex Dirichlet character modulo any nonzero modulus, "
                        + "the product of its standard Gauss sum with the opposite-character, "
                        + "inverse-additive-character Gauss sum equals the modulus. The proof "
                        + "uses the discrete Fourier inversion identity on ZMod N at the "
                        + "negative unit and the primitive-character Fourier transform law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primitive-dirichlet-gauss-normsq-general"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/GeneralDirichletGaussNorm.primitive_dirichlet_gauss_normSq_general"),
                H("General primitive Dirichlet Gauss norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking the complex conjugate form of the product identity gives squared "
                        + "complex modulus exactly equal to N. This covers composite moduli and "
                        + "provides the normalization input for general primitive twists."))),
                DescribeRole.Theorem))));
}
