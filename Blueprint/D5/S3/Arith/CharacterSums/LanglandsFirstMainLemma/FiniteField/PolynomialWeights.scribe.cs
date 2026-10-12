using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField;

internal sealed class SupplierPolynomialWeightsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/epsilonfml2026hassedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multiplicative monic-polynomial weight connecting Gauss sums with closed points.",
        H("Gauss polynomial weight"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supplier-gauss-polynomial-weight"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/PolynomialWeights.gaussPolynomialWeight"),
                H("A character weight on monic polynomials"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For any field k, multiplicative character χ : MulChar k ℂ and additive "
                        + "character ψ : AddChar k ℂ, gaussPolynomialWeight χ ψ is a monoid "
                        + "homomorphism from monic polynomials over k to ℂ. If P has degree d "
                        + "and coefficient a₁ immediately below its leading term, its weight is "
                        + "χ((-1)^d P(0))ψ(-a₁), with a₁ = P.nextCoeff. The constant polynomial "
                        + "1 has weight 1. Products add degrees and next coefficients and "
                        + "multiply constant coefficients, giving multiplicativity. Zero "
                        + "weight is allowed and neither character is required to be nontrivial "
                        + "for this definition."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "EulerProduct consumes the MonicWeight interface to define degree sums "
                    + "and closed-point power sums. In HasseDavenportLift, "
                    + "gaussPolynomialWeight_minpoly_power identifies the weight of an "
                    + "element's minimal polynomial, raised to the remaining tower degree, "
                    + "with its norm/trace character summand. The final proof takes "
                    + "w = gaussPolynomialWeight χ⁻¹ ψ, retaining both coefficient signs.")),
            Paragraph(Text(
                "Source: epsilon_FML at immutable commit "
                    + "b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed, "
                    + "LanglandsFirstMainLemma/FiniteField/PolynomialWeights.lean; Apache-2.0. "
                    + "The exact license and original source hashes are in "
                    + "Library/Fourier/epsilonfml2026hassedavenport.md. This is attributed "
                    + "upstream reuse, with no new theorem or open-problem resolution claimed.")),
            Paragraph(Text(
                "Supplier escape registration remains unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/5214: the original "
                    + "finite-field character/norm/trace telescope has no supplied faithful enrolled "
                    + "template with compiled audit evidence. This narrative does not complete that audit.")))));
}
