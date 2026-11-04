using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class ChenSunOriginalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four branches of Chen-Sun Conjecture1.1(1.11) hold for every prime p>3. In order p=1,5,3,7 modulo8 the residues are 4*(1-(-1)^((p-1)/8)), -2, p+1-(-1)^((h-1)/2)*h, and 2-(-1)^((h-1)/2)*h modulo16. Here h is literally NumberField.classNumber of the proved imaginary quadratic field with its true maximal order. The finite congruences, actual class-number square and odd-h sign identity supply all hypotheses; the fallback zero in originalResidue is proved unreachable. No finite prime cutoff is present. Draft delivery still requires independent formal source review and CI; novelty, priority, official acceptance and unique credit are separate unproved claims.", H("ChenSunOriginal"), Blocks(
            Paragraph(Text("The four branches of Chen-Sun Conjecture1.1(1.11) hold for every prime p>3. In order p=1,5,3,7 modulo8 the residues are 4*(1-(-1)^((p-1)/8)), -2, p+1-(-1)^((h-1)/2)*h, and 2-(-1)^((h-1)/2)*h modulo16. Here h is literally NumberField.classNumber of the proved imaginary quadratic field with its true maximal order. The finite congruences, actual class-number square and odd-h sign identity supply all hypotheses; the fallback zero in originalResidue is proved unreachable. No finite prime cutoff is present. Draft delivery still requires independent formal source review and CI; novelty, priority, official acceptance and unique credit are separate unproved claims.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("chensunoriginal-mod-eight-five"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_five"), H("mod_eight_five"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The p=5 mod8 branch of the original inclusive double sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensunoriginal-mod-eight-one"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_one"), H("mod_eight_one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The p=1 mod8 branch, with the literal natural exponent (p-1)/8."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensunoriginal-imaginaryclassnumber"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunOriginal.imaginaryClassNumber"), H("imaginaryClassNumber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Here h is exactly the cardinality of the ideal class group of the ring of integers of the proved quadratic number field, not a character-sum definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chensunoriginal-mod-eight-three"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_three"), H("mod_eight_three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The p=3 mod8 branch uses the proved actual-class-number square and oddness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensunoriginal-mod-eight-seven"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_seven"), H("mod_eight_seven"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The p=7 mod8 branch, with the same actual maximal-order class number."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chensunoriginal-originalresidue"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunOriginal.originalResidue"), H("originalResidue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The four original residues. The final zero case is unreachable for primes p>3. The class-number branches instantiate the proved field only when p=3 mod4."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chensunoriginal-full-original"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/ChenSunOriginal.full_original"), H("full_original"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Chen-Sun arXiv:2409.08213v4 Conjecture 1.1(1.11), all primes p>3. The double sum is literal (1.8); h in the two odd branches is NumberField.classNumber of the maximal order of Q(sqrt(-p)), identified by PrimeImaginary.sqrtFieldEquiv and PrimeImaginary.maximalOrderEquiv."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/CharacterSums/ChenSunModSixteen")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Zeta/QuadraticClassNumberSquare"))]));
}
