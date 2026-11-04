using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class ChenSunDoubleCharacterDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The defining double sum uses both inclusive natural intervals and the integer symbol of j squared plus j times k. Multiplicativity and reflected prefixes reduce it to a triangle. The genuine restricted Gram norms give exact even and odd energy identities, before any modular or class-number substitution.", H("ChenSunDoubleCharacter"), Blocks(
            Paragraph(Text("The defining double sum uses both inclusive natural intervals and the integer symbol of j squared plus j times k. Multiplicativity and reflected prefixes reduce it to a triangle. The genuine restricted Gram norms give exact even and odd energy identities, before any modular or class-number substitution.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-doublesum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum"), H("doubleSum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Literal equation (1.8) of Chen-Sun arXiv:2409.08213v4; both endpoints are inclusive."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-doublesum-eq-row-sum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum_eq_row_sum"), H("doubleSum_eq_row_sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Multiplicativity changes each summand into the row form used by the Gram identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-twice-doublesum-triangle"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.twice_doubleSum_triangle"), H("twice_doubleSum_triangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Unconditional integral triangular identity for every odd prime; no class-number input."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-columnsum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum"), H("columnSum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Actual column sums of the two restricted character matrices, with integer arguments."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-columnsum-eq-prefix"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum_eq_prefix"), H("columnSum_eq_prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter.columnSum_eq_prefix supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-column-energy"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.column_energy"), H("column_energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Restricted Gram energy transported to the literal natural interval."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-even-columnsum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_columnSum"), H("even_columnSum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The even-case column vector is a+4b, with b an actual integral partialSum quotient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-odd-columnsum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_columnSum"), H("odd_columnSum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The odd-case column vector is -a+4b, with the zero midpoint included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-even-energy-exact"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_energy_exact"), H("even_energy_exact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Exact even-case energy identity. The remaining mod-sixteen step is factorial parity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensundoublecharacter-odd-energy-exact"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_energy_exact"), H("odd_energy_exact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Exact odd-case energy identity, before reflection and factorial parity reduce it modulo 32."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/QuadraticCharacterGram")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixEnergy")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/QuadraticSignProducts"))]));
}
