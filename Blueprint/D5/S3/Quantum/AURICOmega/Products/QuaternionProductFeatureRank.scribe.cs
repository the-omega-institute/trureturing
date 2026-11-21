using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega.Products;

internal sealed class QuaternionProductFeatureRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/Products/QuaternionProductFeatureRank.";

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full Cartesian product of n unit-quaternion readings has least real feature dimension five to the n.",
        H("Feature dimension of a product of quaternion readings"),
        Blocks(
            Describe.Lean(DescribeId.Create("quaternion-product-reading"),
                DeclarationHandle.Create(Prefix + "productReading"),
                H("Reading of two ordered tuples"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiply the n readings in the corresponding positions of the two tuples."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quaternion-product-feature-rank"),
                DeclarationHandle.Create(Prefix + "least_feature_rank"),
                H("Least real feature dimension on the full Cartesian product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("leastFeatureDimension")), Open,
                    Subscript(F.Id("K"), F.Id("n")), Close, Sp, Eq, Sp,
                    D(5), Caret, Grp(F.Id("n"))))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For unit quaternions q and p, the single-factor reading is "
                        + "(1 + inner(q,p))/2. Given any natural number n, compare two ordered "
                        + "n-tuples by multiplying their corresponding factor readings. The least "
                        + "dimension of a real Euclidean space in which all such comparisons are "
                        + "inner products of feature vectors equals 5^n. The empty tuple has reading "
                        + "one and requires one feature coordinate.")),
                    Paragraph(Text(
                        "For one quaternion the normalized feature vector is (1,q)/sqrt(2). "
                        + "Taking all coordinate products gives a Euclidean map with 5^n coordinates. "
                        + "For the opposite bound, sample 1, -1, i, j and k in each coordinate. "
                        + "The single-factor Gram determinant is 1/8. The Gram matrix of the "
                        + "Cartesian grid is its n-fold Kronecker power, which is invertible. "
                        + "Any map realizing the reading must therefore send all 5^n grid points "
                        + "to linearly independent vectors. The lower bound uses the full grid."))),
                DescribeRole.Theorem))));
}
