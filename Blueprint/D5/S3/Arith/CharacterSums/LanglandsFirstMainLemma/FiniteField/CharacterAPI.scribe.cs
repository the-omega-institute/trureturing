using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField;

internal sealed class SupplierCharacterApiDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-field characters, Langlands-normalized Gauss sums, and norm/trace pullback.",
        H("Finite-field character interface"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-langlands-gauss-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.langlandsGaussSum"),
                H("Inverse-character and leading-minus normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a field k with Fintype k, FiniteMulChar k is MulChar k ℂ and "
                        + "FiniteAddChar k is AddChar k ℂ. The definition is "
                        + "langlandsGaussSum χ ψ = -gaussSum χ⁻¹ ψ, equivalently the negative "
                        + "sum of χ⁻¹(x)ψ(x) over kˣ. MulChar has value zero at zero, "
                        + "including the trivial multiplicative character. For ψ ≠ 1, the "
                        + "trivial multiplicative character has normalized Gauss sum 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supplier-norm-character-inverse"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/CharacterAPI.normMulChar_inv"),
                H("Norm pullback commutes with character inversion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For fields k and K, Finite K, Algebra k K, and any χ in FiniteMulChar k, "
                        + "normMulChar k K χ⁻¹ = (normMulChar k K χ)⁻¹. Here normMulChar χ "
                        + "evaluates χ on Algebra.norm k, while traceAddChar ψ evaluates ψ "
                        + "on Algebra.trace k K. Neither definition replaces the norm or trace "
                        + "by an auxiliary function."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "PolynomialWeights consumes FiniteMulChar and FiniteAddChar to construct "
                    + "gaussPolynomialWeight. HasseDavenportLift consumes the Gauss-sum "
                    + "normalization and both pullbacks; its final proof explicitly rewrites "
                    + "by normMulChar_inv. The inverse character and leading minus are "
                    + "required for the power identity in every extension degree. Only the "
                    + "additive character must be nontrivial in the lifting theorem.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/FiniteField/CharacterAPI.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed "
                    + "upstream reuse, with no new theorem or open-problem resolution claimed.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
