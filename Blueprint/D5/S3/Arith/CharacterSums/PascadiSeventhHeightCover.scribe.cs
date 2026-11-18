using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiSeventhHeightCoverDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual integer pencil L₀Qᵢ−LᵢQ₀ has a root-relevant cover by at most three primitive irreducible integer factors under a single seventh-weight height gap. This replaces the old eighth-weight localized-quadratic branch by two proved estimates: actual quadratic pencils use their structural seventh-weight resultant theorem, and a quadratic factor of a genuine cubic uses the sixth-weight mixed resultant theorem. The cubic localized-factor branch and the finite factor-lifting construction are adapted from PascadiPrimeCubeSingularCover.actual_singular_factor_cover. The literal coefficient bounds, common root modulo p³, singularity modulo prime p, baseline L unit and nonzero polynomial reductions all remain explicit. This is an algebraic cover and does not assert a larger tuple-count exponent or the full arbitrary-modulus conjecture.",
        H("Seventh-height actual singular factor cover"),
        Blocks(
            Paragraph(Text("Two localized cubic factors are handled by the original actual residual. When both localized factors are quadratic, one genuine cubic original suffices for the mixed sixth-weight bound. If both originals are quadratic, the actual LQ quadratic elimination supplies the common factor, and the constant complementary factors together with their modular units transfer it to the localized factors. Nonzero singular quadratic reduction ensures that the actual quadratic leading coefficient is nonzero modulo p. No generic factor-height hypothesis replaces the actual LQ coefficient structure. The common factor chosen for every member belongs to the root-relevant factors of one fixed member.")),
            Describe.Lean(DescribeId.Create("pascadi-actual-seventh-height-singular-factor-cover"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover.actual_seventh_height_singular_factor_cover"),
                H("actual_seventh_height_singular_factor_cover"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a family with literal bounds |lᵢ|≤3I, |mᵢ|≤3J, |qᵢ|≤I², |rᵢ|≤2IJ, |sᵢ|≤J², J≤I and J≥1, original polynomial height H≥1, a common root modulo p³, derivative zero modulo p, nonzero reductions, and a unit baseline L, the gap max(10368·3⁹, max(14256, 24(8H)⁴))(IJ)⁷<p⁵ gives a cover by at most three primitive irreducible integer factors of the selected original member. Every factor vanishes at the actual residue root and has nonzero reduction; every original member is divisible by one of them. The proof consumes both the actual quadratic resultant theorem and the improved true-cubic factor estimate."))),
                DescribeRole.Theorem)),
        edges: []));
}
