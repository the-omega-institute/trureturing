using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiQuadraticConstantBaseDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the literal pencil Pᵢ=L₀Qᵢ−LᵢQ₀, assume m₀=s₀=0, prime p, l₀ a unit modulo p, genuine quadratic P₁ and P₂, common root modulo p³ and vanishing derivatives modulo p. Under the actual coefficient bounds |lᵢ|≤3I, |mᵢ|≤3J, |qᵢ|≤I², |rᵢ|≤2IJ, |sᵢ|≤J², with I,J≥1, the height gap 14256 I⁷J⁴<p⁵ forces their quadratic resultant to vanish. The oracle supplied the route of dividing the resultant by the constant baseline before applying the height gap. The independently derived explicit integer quotient gives the smaller constant 14256 without a variable polynomial or differentiation. This algebraic result does not assert the full tuple count, a larger final exponent range, or the arbitrary-modulus conjecture.",
        H("Constant-baseline quadratic singular elimination"),
        Blocks(
            Paragraph(Text("Write Q₀=c+bT and L₀=u. The three quadratic-resultant minors have the forms uH+bcD, uE+b²D and uF+c²D. Their quadratic combination cancels its constant term exactly, leaving the integer quotient u(H²−EF)+D(2bcH−c²E−b²F). Its absolute value is at most 14256 I⁷J⁴. The existing fifth-power divisibility theorem and the unit u allow cancellation of u, so the gap forces the quotient and then the actual resultant to be zero. All auxiliary identities and estimates lie on this proof path; none are separate numerical instances.")),
            Describe.Lean(DescribeId.Create("pascadi-constant-base-quadratic-singular-resultant-zero"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiQuadraticConstantBase.constant_base_quadratic_singular_resultant_zero"),
                H("constant_base_quadratic_singular_resultant_zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("With m₀=s₀=0 and l₀ a unit modulo prime p, two genuine quadratic pencil members sharing a root modulo p³ and singular modulo p have zero quadratic resultant whenever their actual weighted coefficient bounds satisfy 14256 I⁷J⁴<p⁵. Constant Q₀ and vanishing partner coefficients are included. The earlier generic eighth-weight quadratic estimate does not supply this seventh-weight gap."))),
                DescribeRole.Theorem)),
        edges: []));
}
