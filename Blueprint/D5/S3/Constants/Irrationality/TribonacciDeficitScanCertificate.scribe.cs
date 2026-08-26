using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class TribonacciDeficitScanCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        const string declarationPrefix =
            "D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate.";

        var deficitCode = Equal(
            Call("tribonacciDeficit", Id("pair")),
            Call("tribonacciCodeValue", Call("tribonacciDeficitCodeAt10", Id("pair"))));
        var nonintegralCount = Equal(
            Call("card", Id("tribonacciNonintegralScanPairs")),
            Num(8934));
        var genuineNonintegrality = new Formula.Logic(
            new Formula.Relation(
                Id("pair"),
                FormulaRelationOperator.MemberOf,
                Id("tribonacciNonintegralScanPairs")),
            FormulaLogicOperator.Implies,
            new Formula.Not(new Formula.Relation(
                Call("tribonacciDeficit", Id("pair")),
                FormulaRelationOperator.MemberOf,
                new Formula.Integers())));
        var integralComplement = new Formula.Logic(
            new Formula.Logic(
                new Formula.Relation(
                    Id("pair"),
                    FormulaRelationOperator.MemberOf,
                    Id("tribonacciScanPairs")),
                FormulaLogicOperator.And,
                new Formula.Not(new Formula.Relation(
                    Id("pair"),
                    FormulaRelationOperator.MemberOf,
                    Id("tribonacciNonintegralScanPairs")))),
            FormulaLogicOperator.Implies,
            new Formula.Relation(
                Call("tribonacciDeficit", Id("pair")),
                FormulaRelationOperator.MemberOf,
                new Formula.Integers()));
        var exactSpectrum = Equal(
            Call("image", Id("tribonacciDeficitCodeAt10"), Id("tribonacciScanPairs")),
            Id("tribonacciScanSpectrum"));
        var ratio = new Formula.Fraction(Num(8934), Num(20100));
        var percentageInterval = new Formula.Logic(
            new Formula.Relation(
                new Formula.Fraction(Num(4435), Num(10000)),
                FormulaRelationOperator.LessThanOrEqual,
                ratio),
            FormulaLogicOperator.And,
            new Formula.Relation(
                ratio,
                FormulaRelationOperator.LessThan,
                new Formula.Fraction(Num(4445), Num(10000))));
        var strictBound = new Formula.Logic(
            new Formula.Relation(
                Id("pair"),
                FormulaRelationOperator.MemberOf,
                Id("tribonacciScanPairs")),
            FormulaLogicOperator.Implies,
            new Formula.Relation(
                new Formula.Absolute(Call("tribonacciDeficit", Id("pair"))),
                FormulaRelationOperator.LessThan,
                new Formula.Fraction(Num(955), Num(1000))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The triangular Tribonacci scan has a strict bound, an exact nonintegral count, and an exact eight-point cubic spectrum.",
            H("Tribonacci Deficit Scan Certificate"),
            Blocks(
                Paragraph(Text(
                    "On the certified triangular scan, the real deficit agrees with its exact "
                        + "layer-ten cubic code. The nonintegral filter has 8,934 members out of "
                        + "20,100; membership proves genuine real nonintegrality, while every "
                        + "pair in the scan complement has an integral, in fact zero, deficit. "
                        + "The exact ratio 8934/20100 lies in the interval from 0.4435 inclusive "
                        + "to 0.4445 exclusive, so it rounds to 44.4 percent.")),
                Paragraph(Text(
                    "For the same certified pairs, every deficit has absolute value strictly "
                        + "less than 955/1000. Their exact cubic-code image is exactly the listed "
                        + "eight-point spectrum, including zero, so the scan values form this "
                        + "finite discrete spectrum.")),
                Paragraph(Text(
                    "The strict bound and the rounded percentage are proved only for the "
                        + "certified triangular scan 1 <= v1 <= v2 <= 200; they are not "
                        + "unrestricted claims about an unspecified source scan. Outside that "
                        + "scan, those two source claims remain unestablished.")),
                Paragraph(Text(
                    "The certificate does not establish that this spectrum is the trace lattice "
                        + "of the complex conjugate pair. The exact-spectrum theorem is a finite "
                        + "image statement and supplies no conjugate-pair trace map or lattice "
                        + "identification.")),
                Describe.Lean(
                    DescribeId.Create("the-real-deficit-agrees-with-the-exact-code"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_scan_deficit_eq_code"),
                    H("The real deficit agrees with the exact code"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(deficitCode)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This bridge is restricted to pairs in the certified scan and connects "
                            + "the implemented Binet deficit to the finite exact computation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-nonintegral-filter-has-eight-thousand-nine-hundred-thirty-four-members"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_nonintegral_scan_count"),
                    H("The nonintegral filter has 8,934 members"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nonintegralCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Four kernel-checked row blocks sum to the exact count for the fixed "
                            + "triangular window."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("filter-membership-is-genuine-nonintegrality"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_nonintegral_of_mem_scan"),
                    H("Filter membership is genuine nonintegrality"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(genuineNonintegrality)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A nonzero exact quadratic coordinate is carried through the code-value "
                            + "bridge to rule out equality with every integer."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-scan-complement-is-integral"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_integral_of_mem_scan_complement"),
                    H("The scan complement is integral"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(integralComplement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "On this finite spectrum, a zero quadratic coordinate forces the whole "
                            + "code to be zero, so the complement contributes no additional "
                            + "nonintegral deficits."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-exact-ratio-rounds-to-forty-four-point-four-percent"),
                    DeclarationHandle.Create(
                        declarationPrefix
                            + "tribonacci_nonintegral_scan_percentage_rounds_to_44_4"),
                    H("The exact ratio rounds to 44.4 percent"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(percentageInterval)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The theorem proves the rational half-open rounding interval directly; "
                            + "it does not rely on floating-point evaluation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-code-image-is-the-eight-point-spectrum"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_scan_spectrum_exact"),
                    H("The code image is the eight-point spectrum"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(exactSpectrum)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Inclusion is certified across all four row blocks, and explicit scan "
                            + "witnesses show that every listed cubic code occurs."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("every-certified-deficit-obeys-the-strict-bound"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_deficit_scan_bound"),
                    H("Every certified deficit obeys the strict bound"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(strictBound)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The strict inequality is proved for each spectral code and transferred "
                            + "to every pair in the certified triangular scan."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/TribonacciDeficitScan")),
            ]));
    }
}
