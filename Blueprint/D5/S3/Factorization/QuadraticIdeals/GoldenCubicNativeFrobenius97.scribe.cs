using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeFrobenius97Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five actual native Frobenius squareclasses are independent at the common good prime 97.",
        H("Native Frobenius squareclass independence at 97"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-frobenius97-row-nonsquare"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.at97_auxiliary_nonsquare"),
                H("The observed prime is nonsquare in every auxiliary row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The prime 97 has character -1 at 5, 7, 13, 19 and 29. These are the rows of the binary certificate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-frobenius97-native-point-counts"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_good_count"),
                H("Five actual good-reduction point counts at 97"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All five curves are smooth modulo 97. Their group carriers have 88, 101, 103, 107 and 100 points, including infinity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-frobenius97-native-discriminants"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.nativeDiscriminant97_eq"),
                H("Frobenius discriminants computed from those native point counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace discriminants are -288, -379, -363, -307 and -384; they are not the Weierstrass discriminants."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-frobenius97-native-squareclass-independence"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97.native_at97_not_isSquare_product"),
                H("Five native Frobenius squareclasses are independent over the rationals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonempty finite subset has nonsquare product. The five-row Legendre matrix and its checked binary left inverse certify this one-prime result, not a general density or lifting theorem."))), DescribeRole.Theorem))));
}
