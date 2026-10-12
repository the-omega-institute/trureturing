using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField;

internal sealed class LanglandsFirstMainLemmaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Langlands-normalized Hasse–Davenport lift for finite-field Gauss sums.",
        H("Langlands-normalized Hasse–Davenport lifting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("langlands-hasse-davenport-lift"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.hasseDavenportLift"),
                H("Hasse–Davenport lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For fields k and K with finite underlying types, an algebra structure, "
                            + "a finite multiplicative character χ, and a finite additive character ψ "
                            + "with ψ unequal to the trivial character, the theorem identifies the "
                            + "Langlands-normalized Gauss sum after norm and trace pullback with the "
                            + "base Gauss sum raised to the finite extension degree. The multiplicative "
                            + "character is unrestricted, so the trivial multiplicative character is "
                            + "included.")),
                    Paragraph(Text(
                        "The normalization is langlandsGaussSum(χ, ψ) = -gaussSum(χ⁻¹, ψ). "
                            + "The theorem and proof are reused from epsilon_FML at "
                            + "commit b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed. The argument identifies closed-point contributions through "
                            + "minimal polynomials and actual algebraic norm and trace, then uses "
                            + "the Euler product to obtain the power identity. The inverse character "
                            + "and leading minus sign cancel the ordinary lifting parity sign in every "
                            + "degree. This supplies the classical Hasse–Davenport theorem through "
                            + "attributed upstream reuse."))),
                DescribeRole.Theorem))));
}
