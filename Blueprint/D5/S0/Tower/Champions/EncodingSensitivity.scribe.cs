using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class EncodingSensitivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var binary = Id("binary");
        var coding = Id("coding");
        var codingSystem = Id("CodingSystem");
        var fingerprint = Id("codingFingerprintFor");
        var tribonacci = Id("tribonacci");
        var tribonacciFirstDigitName = Id("tribonacciFirstDigitName");
        var zeckendorf = Id("zeckendorf");

        var fingerprintDefinition = new Formula.Logic(
            Equal(Call("codingFingerprintFor", binary), Id("binaryCodingFingerprint")),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(
                    Call("codingFingerprintFor", zeckendorf),
                    Id("zeckendorfCodingFingerprint")),
                FormulaLogicOperator.And,
                Equal(
                    Call("codingFingerprintFor", tribonacci),
                    Id("tribonacciCodingFingerprint"))));
        var decodedValueDefinition = new Formula.Logic(
            Equal(
                Call("firstPlaceDecodedValue", binary),
                new Formula.Power(Num(2), Num(0))),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(
                    Call("firstPlaceDecodedValue", zeckendorf),
                    Call("wValue", Num(0))),
                FormulaLogicOperator.And,
                Equal(
                    Call("firstPlaceDecodedValue", tribonacci),
                    Call("decode", tribonacciFirstDigitName))));
        var encodingSensitive = Call("Injective", fingerprint);
        var encodingBlind = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("coding"), codingSystem)],
            Equal(Call("firstPlaceDecodedValue", coding), Num(1)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Coding fingerprints distinguish binary, Zeckendorf, and Tribonacci coding, "
                + "while their occupied first places all decode to the same unit value.",
            H("Encoding-Sensitive and Encoding-Blind Quantities"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("coding-fingerprint-for"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/EncodingSensitivity.codingFingerprintFor"),
                    H("Fingerprint indexed by coding system"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fingerprintDefinition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The indexed function selects the already frozen binary, Zeckendorf, "
                            + "or Tribonacci coding fingerprint without changing its value."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("first-place-decoded-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/EncodingSensitivity.firstPlaceDecodedValue"),
                    H("First-place decoded value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decodedValueDefinition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is not a constant function by definition: its three branches use "
                            + "the binary positional weight, the Zeckendorf weight carrier, and "
                            + "the Tribonacci representation decoder, respectively."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("coding-fingerprint-is-encoding-sensitive"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/EncodingSensitivity."
                            + "coding_fingerprint_is_encoding_sensitive"),
                    H("The fingerprint distinguishes coding systems"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(encodingSensitive)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Injectivity packages the frozen pairwise inequalities as sensitivity: "
                            + "equal fingerprint values force equal coding-system indices."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("first-place-decoded-value-is-encoding-blind"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/EncodingSensitivity."
                            + "first_place_decoded_value_is_encoding_blind"),
                    H("First-place decoding is encoding-blind"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(encodingBlind)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every member of the three-coding index, the independently "
                                + "computed occupied first place decodes to one.")),
                        Paragraph(Text(
                            "This is an S0 parsing-layer comparison. It does not identify any "
                                + "zeta-layer object: zeta declarations live at S3 and the S0 "
                                + "coding interfaces provide no permitted bridge to them."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/CodingFingerprint")),
            ]));
    }
}
