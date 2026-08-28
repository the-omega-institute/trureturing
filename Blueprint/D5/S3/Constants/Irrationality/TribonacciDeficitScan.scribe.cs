using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class TribonacciDeficitScanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        const string declarationPrefix =
            "D5/S3/Constants/Irrationality/TribonacciDeficitScan.";

        var sourceNormalization = Equal(
            Id("tribonacciBinetNameValue"),
            Id("sourceNormalizedBinetValue"));
        var scanCount = Equal(Call("card", Id("tribonacciScanPairs")), Num(20100));
        var coordinateCriterion = new Formula.Logic(
            NotEqual(Call("quadratic", Id("x")), Num(0)),
            FormulaLogicOperator.Implies,
            new Formula.Not(new Formula.Relation(
                Call("tribonacciCodeValue", Id("x")),
                FormulaRelationOperator.MemberOf,
                new Formula.Integers())));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The implemented Tribonacci deficit uses the source-normalized Binet leading term on an exact triangular scan.",
            H("Tribonacci Deficit Scan"),
            Blocks(
                Paragraph(Text(
                    "The implemented quantity assigns a canonical no-111 Tribonacci name to "
                        + "each natural number, evaluates the occupied digits with the frozen "
                        + "Binet leading coefficient, and defines the addition deficit as the "
                        + "two readings minus the reading of their sum. The normalization bridge "
                        + "identifies that value with the source's shifted Binet coefficient. "
                        + "Thus the deficit is computed from the Binet leading term for this "
                        + "implemented definition.")),
                Paragraph(Text(
                    "The finite domain used by the certificate is exactly the triangular scan "
                        + "1 <= v1 <= v2 <= 200, containing 20,100 pairs. Exact cubic arithmetic "
                        + "keeps the scan symbolic, and a nonzero quadratic coordinate is a "
                        + "certificate of genuine real nonintegrality at the Tribonacci root.")),
                Describe.Lean(
                    DescribeId.Create("the-binet-face-has-the-source-normalization"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacciBinetNameValue_eq_source_normalization"),
                    H("The Binet face has the source normalization"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(sourceNormalization)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The equality uses the existing exact normalization bridge; it does not "
                            + "reconstruct the coefficient from a decimal approximation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-triangular-scan-has-twenty-thousand-one-hundred-pairs"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_scan_pair_count"),
                    H("The triangular scan has 20,100 pairs"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(scanCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the cardinality of the fixed window 1 <= v1 <= v2 <= 200, not "
                            + "the size of an unrestricted or externally supplied scan."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("a-quadratic-coordinate-certifies-nonintegrality"),
                    DeclarationHandle.Create(
                        declarationPrefix
                            + "tribonacci_code_value_not_integer_of_quadratic_ne_zero"),
                    H("A quadratic coordinate certifies nonintegrality"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(coordinateCriterion)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The proof rules out an integer value at the real Tribonacci root rather "
                            + "than treating a symbolic coordinate test as sufficient by itself."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/TribonacciIrrationality")),
            ]));
    }
}
