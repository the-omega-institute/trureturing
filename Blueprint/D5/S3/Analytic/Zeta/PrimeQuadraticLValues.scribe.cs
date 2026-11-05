using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class PrimeQuadraticLValuesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The character is the actual integer quadratic character mapped to complex coefficients. Nontriviality and prime modulus prove primitivity. Doubling least representatives, with the genuine L(0) finite evaluation, gives the lower-half sum (2-chi(2))*L(0). The L(0) supplier is the existing attributed Yao Xu/cadamcat port, not newly authored source.", H("PrimeQuadraticLValues"), Blocks(
            Paragraph(Text("The character is the actual integer quadratic character mapped to complex coefficients. Nontriviality and prime modulus prove primitivity. Doubling least representatives, with the genuine L(0) finite evaluation, gives the lower-half sum (2-chi(2))*L(0). The L(0) supplier is the existing attributed Yao Xu/cadamcat port, not newly authored source.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("primequadraticlvalues-primecharacter"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/PrimeQuadraticLValues.primeCharacter"), H("primeCharacter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The same integer-valued quadratic character as in the Legendre symbol, mapped to the coefficient field used by Mathlib's L-functions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primequadraticlvalues-primecharacter-quadratic"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/PrimeQuadraticLValues.primeCharacter_quadratic"), H("primeCharacter_quadratic"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Analytic.Zeta.PrimeQuadraticLValues.primeCharacter_quadratic supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primequadraticlvalues-primecharacter-nontrivial"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/PrimeQuadraticLValues.primeCharacter_nontrivial"), H("primeCharacter_nontrivial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Analytic.Zeta.PrimeQuadraticLValues.primeCharacter_nontrivial supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primequadraticlvalues-primecharacter-primitive"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/PrimeQuadraticLValues.primeCharacter_primitive"), H("primeCharacter_primitive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Analytic.Zeta.PrimeQuadraticLValues.primeCharacter_primitive supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primequadraticlvalues-primecharacter-odd"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/PrimeQuadraticLValues.primeCharacter_odd"), H("primeCharacter_odd"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean declaration D5.S3.Analytic.Zeta.PrimeQuadraticLValues.primeCharacter_odd supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primequadraticlvalues-half-sum-eq-lfunction-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/PrimeQuadraticLValues.half_sum_eq_LFunction_zero"), H("half_sum_eq_LFunction_zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A finite doubling argument gives the half-interval sum from the actual analytic L(0). This theorem uses no class-number parameter or class-number identity."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Zeta/QuadraticLValueSquare")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Analytic/Zeta/CatalanPrimeOddMoment"))]));
}
