using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiLocalizedFactorDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrated from the completed pinned singular-cover formalization. Primitive integer factors are selected at the actual residue root and inherit weighted coefficient control. The complementary polynomial after real rescaling is not asserted to be integral. The proof uses the repository Gelfond inequality. The rational-factor lifting helper is exposed for the live prime-cube proof.",
        H("Primitive localized factors"),
        Blocks(
            Paragraph(Text("Integrated from the completed pinned singular-cover formalization. Primitive integer factors are selected at the actual residue root and inherit weighted coefficient control. The complementary polynomial after real rescaling is not asserted to be integral. The proof uses the repository Gelfond inequality. The rational-factor lifting helper is exposed for the live prime-cube proof.")),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-localized-factor-primitive-localized-factor"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.primitive_localized_factor"), H("primitive_localized_factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The factor is constructed from the original polynomial, preserving exact singularity data."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-localized-factor-weighted-primitive-localized-factor"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_primitive_localized_factor"), H("weighted_primitive_localized_factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Weighted height is inherited by the primitive factor selected at the actual residue root."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-localized-factor-lift-primitive-rational-factor"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.lift_primitive_rational_factor"), H("lift_primitive_rational_factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("lift primitive rational factor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-localized-factor-weighted-localized-factor-cover"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiLocalizedFactor.weighted_localized_factor_cover"), H("weighted_localized_factor_cover"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The cover consists of primitive integer factors of actual original polynomials, and every chosen factor vanishes at the actual residue root."))), DescribeRole.Theorem)),
        edges: []));
}
