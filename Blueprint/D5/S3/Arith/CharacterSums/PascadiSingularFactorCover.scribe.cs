using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiSingularFactorCoverDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrated from the completed pinned singular-cover formalization. Explicit weighted determinant bounds, singular resultant divisibility and rational factorization give a small factor cover under their stated hypotheses. The cover alone does not count original six-letter tuples. Necessary rational-factor helpers are exposed publicly for canonical integration; their proofs are retained from the archive.",
        H("Weighted singular factor cover"),
        Blocks(
            Paragraph(Text("Integrated from the completed pinned singular-cover formalization. Explicit weighted determinant bounds, singular resultant divisibility and rational factorization give a small factor cover under their stated hypotheses. The cover alone does not count original six-letter tuples. Necessary rational-factor helpers are exposed publicly for canonical integration; their proofs are retained from the archive.")),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-singular-factor-cover-weighted-resultant-estimate"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSingularFactorCover.weighted_resultant_estimate"), H("weighted_resultant_estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual resultant has the Sylvester determinant's exact weighted height."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-singular-factor-cover-integer-weighted-resultant-bound"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSingularFactorCover.integer_weighted_resultant_bound"), H("integer_weighted_resultant_bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Uniform explicit height bound for degree two or three integer polynomials. The coefficient hypotheses are weighted; the resultant bound is proved from them."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-singular-factor-cover-weighted-singular-resultant-zero"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSingularFactorCover.weighted_singular_resultant_zero"), H("weighted_singular_resultant_zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The explicit weighted height gap and singular divisibility force zero resultant."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-singular-factor-cover-rational-factor-card-le"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSingularFactorCover.rational_factor_card_le"), H("rational_factor_card_le"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("rational factor card le."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-singular-factor-cover-rational-common-factor-of-resultant-zero"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSingularFactorCover.rational_common_factor_of_resultant_zero"), H("rational_common_factor_of_resultant_zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("rational common factor of resultant zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-pascadi-singular-factor-cover-weighted-singular-factor-cover"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiSingularFactorCover.weighted_singular_factor_cover"), H("weighted_singular_factor_cover"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A singular family satisfying the proved height bound has a cover by at most three irreducible rational factors of any fixed member. No local root property of the chosen common factor is asserted."))), DescribeRole.Theorem)),
        edges: []));
}
