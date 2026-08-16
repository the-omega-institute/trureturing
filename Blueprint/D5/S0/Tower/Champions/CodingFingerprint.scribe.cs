using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class CodingFingerprintDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = Id("a");
        var decoded = Id("decodedValue");
        var leading = Id("leadingMainTerm");
        var phi = Id("phi");
        var rBinary = Id("rBinary");
        var rTribonacci = Id("rTribonacci");
        var rZeckendorf = Id("rZeckendorf");
        var reals = Id("R");
        var scale = Id("scale");
        var t = Id("t");
        var tSquared = new Formula.Power(t, Num(2));
        var shiftedDenominator = Subtract(
            Subtract(Multiply(Num(3), tSquared), Multiply(Num(2), t)),
            Num(1));
        var shiftedCoefficient = new Formula.Fraction(tSquared, shiftedDenominator);
        var zeckendorfValue = new Formula.Fraction(
            new Formula.Power(phi, Num(2)),
            Call("sqrt", Num(5)));

        Formula Fingerprint(Formula mainTerm, Formula decodedValue) =>
            new Formula.Fraction(mainTerm, decodedValue);

        var definition = Equal(Id("codingFingerprint"), Fingerprint(leading, decoded));
        var scaleInvariant = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("leadingMainTerm"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("decodedValue"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("scale"), reals),
            ],
            new Formula.Logic(
                NotEqual(scale, Num(0)),
                FormulaLogicOperator.Implies,
                Equal(
                    Fingerprint(Multiply(scale, leading), Multiply(scale, decoded)),
                    Fingerprint(leading, decoded))));
        var bridge = Equal(shiftedCoefficient, Multiply(a, t));
        var binaryValue = Equal(rBinary, Num(1));
        var tribonacciValue = Equal(
            rTribonacci,
            Multiply(shiftedCoefficient, tSquared));
        var zeckendorfFingerprintValue = Equal(rZeckendorf, zeckendorfValue);
        var pairwiseDistinct = new Formula.Logic(
            NotEqual(rBinary, rZeckendorf),
            FormulaLogicOperator.And,
            new Formula.Logic(
                NotEqual(rBinary, rTribonacci),
                FormulaLogicOperator.And,
                NotEqual(rZeckendorf, rTribonacci)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The first-place Binet main term divided by its decoded value distinguishes three coding systems.",
            H("Coding Spectrum Fingerprint"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("coding-fingerprint-definition"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/CodingFingerprint.codingFingerprint"),
                    H("Scale-independent coding fingerprint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(definition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The fingerprint is the leading first-place expansion main term divided "
                            + "by the value decoded from that first place."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("coding-fingerprint-scale-invariance"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/CodingFingerprint."
                        + "coding_fingerprint_scale_invariant"),
                    H("Common rescaling does not change the fingerprint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(scaleInvariant)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Multiplying both the Binet main term and the decoded value by one "
                            + "nonzero scale cancels exactly in the quotient."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-binet-normalization-bridge"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/CodingFingerprint."
                        + "tribonacci_binet_normalization_bridge"),
                    H("The shifted Tribonacci coefficient is the frozen coefficient times t"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(bridge)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The derivative-form coefficient for powers t to n minus one equals "
                            + "the frozen coefficient for powers t to n multiplied by t. The "
                            + "proof uses the frozen Tribonacci cubic equation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("binary-coding-fingerprint-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/CodingFingerprint."
                        + "binary_coding_fingerprint_value"),
                    H("Binary fingerprint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(binaryValue)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The first binary main term and its decoded positional weight are both one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zeckendorf-coding-fingerprint-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/CodingFingerprint."
                        + "zeckendorf_coding_fingerprint_value"),
                    H("Zeckendorf fingerprint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(zeckendorfFingerprintValue)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The first Zeckendorf position decodes to Fib two, hence to one, while "
                            + "its exact Perron main term is phi squared over square root five."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-coding-fingerprint-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/CodingFingerprint."
                        + "tribonacci_coding_fingerprint_value"),
                    H("Tribonacci fingerprint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(tribonacciValue)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The occupied first Tribonacci digit decodes to one through the frozen "
                            + "representation carrier, leaving the shifted Binet coefficient "
                            + "times t squared."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("coding-fingerprint-values-pairwise-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/CodingFingerprint."
                        + "coding_fingerprint_values_pairwise_distinct"),
                    H("The three coding fingerprints are pairwise distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pairwiseDistinct)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Exact ordered-field estimates give one below the Zeckendorf value, the "
                            + "Zeckendorf value below two, and two below the Tribonacci value."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/GoldenNames")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Binet")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Representation")),
            ]));
    }
}
