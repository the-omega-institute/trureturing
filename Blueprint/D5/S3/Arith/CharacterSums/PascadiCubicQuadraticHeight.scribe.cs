using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiCubicQuadraticHeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "If an integer cubic P=RU has genuine degree three and R has degree two, its complementary factor U is linear. Scaling the variable by I/J, with I≥J≥1, gives supNorm(Uscaled)≥I/J from its nonzero integer leading coefficient. The existing Gelfond product inequality therefore improves the quadratic factor height from 8C I^(3−j)J^j to 8C I^(2−j)J^(j+1). This stronger estimate is used here to bound its resultant with an arbitrary quadratic of the original 8C height by 24(8C)^4(IJ)^6. The statement does not apply the improvement to an original polynomial of degree two and does not assert the full original tuple count or arbitrary-modulus conjecture.",
        H("Quadratic factors of genuine cubic pencils"),
        Blocks(
            Paragraph(Text("The extra factor J/I follows from the linear complementary factor, rather than from primitivity or a stronger general quadratic factor theorem. The scaled Gelfond argument is adapted from PascadiLocalizedFactor.weighted_factor_coeff. The mixed resultant then uses the explicit quadratic formula: its three minors have weights I³J³, I²J⁴ and I⁴J². Their quadratic combination has weight I⁶J⁶. Thus the new factor estimate is consumed on the proof path of a genuine mixed resultant estimate.")),
            Describe.Lean(DescribeId.Create("pascadi-cubic-quadratic-factor-height"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiCubicQuadraticHeight.cubic_quadratic_factor_height"),
                H("cubic_quadratic_factor_height"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For P=RU over the integers with degrees three and two respectively, I≥J≥1 and C≥0, the weighted coefficient bound C I^(3−j)J^j on P implies |Rⱼ|≤8C I^(2−j)J^(j+1). No primitivity or modular-root assumption is needed. The genuine cubic degree is essential to the proof."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-cubic-quadratic-mixed-resultant-height"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiCubicQuadraticHeight.cubic_quadratic_mixed_resultant_height"),
                H("cubic_quadratic_mixed_resultant_height"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The improved quadratic factor R of a genuine cubic P has quadratic resultant at most 24(8C)^4(IJ)^6 against any genuine quadratic S satisfying the original weighted bound 8C I^(3−j)J^j. The proof explicitly consumes cubic_quadratic_factor_height and preserves fixed degree (2,2)."))),
                DescribeRole.Theorem)),
        edges: []));
}
