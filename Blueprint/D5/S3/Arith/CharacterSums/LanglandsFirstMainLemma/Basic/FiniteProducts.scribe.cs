using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.Basic;

internal sealed class SupplierFiniteProductsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-field power sums and products in the retained character-sum supplier.",
        H("Prime-field finite products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-prime-field-power-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.sum_primeField"),
                H("Power sums in an injective unit realization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a prime p, a natural exponent r, a commutative domain R, and an "
                        + "injective group homomorphism ω from (ZMod p)ˣ to Rˣ, the sum of "
                        + "(ω(j) : R)^r over all j is p - 1 cast into R if p - 1 divides r, "
                        + "and is zero otherwise. The homomorphism j ↦ (ω(j) : R)^r is trivial "
                        + "exactly in the divisible case; character orthogonality gives the sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supplier-prime-field-scaled-product"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/Basic/FiniteProducts.prod_one_add_primeField"),
                H("Scaled prime-field product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a field K of characteristic p and any ρ in K, the product over "
                        + "j in ZMod p of 1 + cast(j)ρ equals 1 - ρ^(p - 1). The proof rescales "
                        + "the factorization of X^p - X; ρ = 0 is included separately."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This module imports Mathlib directly. CharacterAPI imports this module, "
                    + "and HasseDavenportLift imports CharacterAPI. "
                    + "This is a retained import dependency. Neither displayed prime-field identity "
                    + "is invoked by the selected Hasse–Davenport proof; the lifting argument uses "
                    + "general finite-field characters and monic-polynomial weights.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/Basic/FiniteProducts.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. These are attributed "
                    + "upstream results, with no new theorem or open-problem resolution claimed.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
