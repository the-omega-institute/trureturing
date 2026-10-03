using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.NumberField;

internal sealed class ZetaProductArithmeticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zeta Product Arithmetic.",
        H("Zeta Product Arithmetic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("galois-character"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacter"),
                H("galois Character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A character of Gal(L/K) valued in ℂ^×."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("galois-character-on-ideal"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.galoisCharacterOnIdeal"),
                H("galois Character On Ideal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The multiplicative extension of a Galois character χ to the nonzero ideals of 𝓞 K " +
                    "(Sharifi Notation 7.1.17): on a prime 𝔭 it is χ(Frob 𝔭) if 𝔭 is unramified in L and 0 " +
                    "otherwise, extended completely multiplicatively via the prime factorisation. The " +
                    "L-function coefficient χ(𝔞)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frobenius-ideal"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.frobeniusIdeal"),
                H("frobenius Ideal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The Gal(L/K)-valued completely-multiplicative ideal Frobenius: on a prime 𝔭 it is the " +
                    "chosen representative (frobeniusClass K L 𝔭).out of the Frobenius conjugacy class (a " +
                    "genuine group element since Gal(L/K) is abelian, so the class is a singleton), " +
                    "extended completely multiplicatively over the prime factorisation. Companion of " +
                    "galoisCharacterOnIdeal: the character value is χ applied to this element (Helper 1). " +
                    "The Multiset.prod over the (unordered) prime factors needs commutativity, supplied by " +
                    "IsMulCommutative Gal(L/K)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unramified-in-of-coprime-abs-norm"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic.unramifiedIn_of_coprime_absNorm"),
                H("Zeta Product Arithmetic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A nonzero prime of 𝓞 K whose norm is coprime to m is unramified in L = K(μ_m): a " +
                    "ramified prime would divide the different ideal, which divides (aeval ζ (minpoly 𝓞K " +
                    "ζ).derivative) by the conductor formula; since minpoly ∣ X^m − 1, that derivative " +
                    "value divides m·ζ^{m−1}, so m ∈ 𝔓, hence (m) ≤ 𝔭 and N𝔭 ∣ N((m)) = m^d, contradicting " +
                    "coprimality."))),
                DescribeRole.Theorem)
        )));
}
