using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiPrimeSquareHyperbolaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed divisors of nonzero integer products bound the prime-square middle word in its literal affine box.",
        H("Divisor counts for the prime-square word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pascadi-prime-square-hyperbola-box"),
                DeclarationHandle.Create(Prefix + "shifted_hyperbola_box_card_le"),
                H("Count all integer points in the shifted box"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix a modulus q > 1, an integer t > 0 whose residue is a unit, a unit target C, "
                        + "and two integer shifts A₁,A₂. Suppose uᵢ represents t Aᵢ modulo q and b represents "
                        + "t(C − A₁ A₂). The two literal integer intervals lie within absolute radii X₁,X₂.")),
                    Paragraph(Text(
                        "For each shifted product congruence solution, the cleared expression "
                        + "t a₁ a₂ + u₂ a₁ + u₁ a₂ is b + kq for a unique integer k. The coordinate radii "
                        + "give |k| at most the floor of (t X₁ X₂ + |u₂| X₁ + |u₁| X₂ + |b|)/q. "
                        + "In this level the shifted integer factors have product nₖ = u₁ u₂ + t(b + kq). "
                        + "It reduces to the unit t² C, so the product is nonzero. The first factor "
                        + "injects the level into the signed divisors of nₖ. Summing twice the positive "
                        + "divisor count of |nₖ| over the admissible levels bounds the full box count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-middle-word-unit-hyperbola"),
                DeclarationHandle.Create(Prefix + "middle_word_unit_hyperbola"),
                H("The actual middle word gives a unit target"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "In ZMod(p²) for prime p, let x₁ + x₂ + z = d x₁ x₂ z and assume x₁ + z "
                        + "and x₂ + z are nonzero modulo p. Then (d z x₁ − 1)(d z x₂ − 1) = 1 + d z² "
                        + "and the right side is a unit. If its reduction vanished, the factored equation "
                        + "would make one of the two reduced factors vanish in the field. Combining that "
                        + "vanishing with 1 + d z² = 0 modulo p gives the corresponding forbidden pair sum.")),
                    Paragraph(Text(
                        "In reduced slope-lattice coordinates with xᵢ = E₁ aᵢ + F₁ bᵢ, unit d, z and E₁ "
                        + "allow division by (d z E₁)² and give shifts of exactly the type counted above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-prime-square-approximation"),
                DeclarationHandle.Create(Prefix + "prime_square_simultaneous_approximation"),
                H("Choose a common unit approximation multiplier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For positive P₁,P₂ with P₁P₂ < p, partition pairs of least representatives "
                        + "modulo p² into P₁P₂ bins. Among the first P₁P₂ + 1 multiples of the two "
                        + "shifts, two lie in the same bin. Their positive multiplier difference t "
                        + "lies below p and is a unit modulo p². The coordinate differences uᵢ "
                        + "represent t times the shifts and satisfy |uᵢ|Pᵢ < p²."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-middle-word-affine-box"),
                DeclarationHandle.Create(Prefix + "middle_word_affine_box_card_le"),
                H("Count the actual middle word in an affine box"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix xᵢ = E aᵢ + vᵢ over ZMod(p²) with E and d z units, and let the aᵢ "
                        + "range over the prescribed integer intervals. Retain the middle-word "
                        + "solutions whose two pair sums xᵢ + z are nonzero modulo p.")),
                    Paragraph(Text(
                        "After factoring the word, division by (d z E)² gives the two shifts. "
                        + "When the retained set is nonempty, any point of it certifies that the "
                        + "normalized target is a unit. Choose the common multiplier from the "
                        + "approximation step and take b to be the least residue of the cleared "
                        + "constant. The divisor sum for the shifted box then bounds the retained "
                        + "count with those same parameters. For an empty retained set the bound "
                        + "holds with the same choice of parameters."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The weighted asymptotic estimate also requires bounds for the reduced slope "
                + "lattice and the Fejér tails.")))));
}
