using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class ChenSunModSixteenDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common factorial product fixes the odd central half-sum parity and the even correction parity. Substitution in the exact energies yields d=-2m^2 modulo16 for every prime p=4m+1 and 2d=c^2+4m^2-3 modulo32 for every prime p=4m+3. The modulus32 is retained until the final factor-two cancellation.", H("ChenSunModSixteen"), Blocks(
            Paragraph(Text("The common factorial product fixes the odd central half-sum parity and the even correction parity. Substitution in the exact energies yields d=-2m^2 modulo16 for every prime p=4m+1 and 2d=c^2+4m^2-3 modulo32 for every prime p=4m+3. The modulus32 is retained until the final factor-two cancellation.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("chensunmodsixteen-odd-half-sum-parity"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_half_sum_parity"), H("odd_half_sum_parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The factorial-product parity of the odd-case central quotient sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensunmodsixteen-even-half-sum-parity"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_half_sum_parity"), H("even_half_sum_parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The same factorial product also fixes the even-case correction parity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensunmodsixteen-odd-doublesum-mod32"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_doubleSum_mod32"), H("odd_doubleSum_mod32"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The class-number-free odd-prime-family congruence retains the factor two, which is essential for subsequently cancelling the modulus from 32 to 16."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensunmodsixteen-even-doublesum-mod16"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_doubleSum_mod16"), H("even_doubleSum_mod16"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The even-prime-family congruence includes every p congruent to one modulo four."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/QuadraticPrefixParity"))]));
}
