using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class QuadraticCharacterGramDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing conic-counting quadratic-character sum gives shifted correlation. Pairing nonzero residues with their negatives restricts the full correlation to the true lower half. Expanding the two sign choices gives the integral Gram and column-energy identities.", H("QuadraticCharacterGram"), Blocks(
            Paragraph(Text("The existing conic-counting quadratic-character sum gives shifted correlation. Pairing nonzero residues with their negatives restricts the full correlation to the true lower half. Expanding the two sign choices gives the integral Gram and column-energy identities.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-correlation"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.correlation"), H("correlation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Correlation of two translates, including the diagonal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-sum-even"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_even"), H("sum_even"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An even function sums twice over any genuine choice of one element from each nonzero negation pair. All partition hypotheses are explicit and none is a Gram assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-restricted-gram"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_gram"), H("restricted_gram"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The restricted row Gram identity used for both signs in the Chen-Sun argument. The left side is an actual finite sum; the only geometric input is a half-set partition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-restricted-column-energy"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_column_energy"), H("restricted_column_energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Summing the restricted Gram identity gives the integral energy of the column sums. This is the common energy identity for the even and odd prime families."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-primehalf"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf"), H("primeHalf"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual lower half of the nonzero residues, selected by least natural representatives."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-prime-restricted-gram"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_restricted_gram"), H("prime_restricted_gram"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Specialization to the genuine lower-half residue set for every odd prime. No half-set or correlation condition is assumed in this prime statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-sum-primehalf"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_primeHalf"), H("sum_primeHalf"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The residue half-set is precisely the positive interval, with its least representatives."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-primehalf-card"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf_card"), H("primeHalf_card"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Arith.CharacterSums.QuadraticCharacterGram.primeHalf_card supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-prime-half-character-cancellation"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_half_character_cancellation"), H("prime_half_character_cancellation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Pairing the complete zero-sum quadratic character gives cancellation of its half sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticcharactergram-prime-column-energy"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_column_energy"), H("prime_column_energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Actual half-residue column energy for every odd prime. Its hypotheses contain neither an assumed Gram identity nor an assumed norm formula."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FiniteFieldQuadraticCharacterSum"))]));
}
