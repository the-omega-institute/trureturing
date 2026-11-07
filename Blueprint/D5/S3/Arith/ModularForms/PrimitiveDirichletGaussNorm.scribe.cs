using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class PrimitiveDirichletGaussNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Gauss sum of a primitive Dirichlet character modulo a prime has squared complex modulus equal to that prime.",
        H("Primitive Dirichlet Gauss norm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primitive-dirichlet-gauss-normsq"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/PrimitiveDirichletGaussNorm.primitive_dirichlet_gauss_normSq"),
                H("Prime-modulus primitive Dirichlet Gauss norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural prime p, a nonzero modulus instance, and a primitive character "
                        + "χ : DirichletCharacter ℂ p, the squared complex modulus of the standard "
                        + "additive-character Gauss sum is p. The proof combines Mathlib's primitive "
                        + "Gauss product with conjugation of both characters and the identity "
                        + "Fintype.card (ZMod p) = p. This is the normalization bridge for primitive "
                        + "Dirichlet modular-form twists; the q-expansion coefficient law remains open."))),
                DescribeRole.Theorem))));
}
