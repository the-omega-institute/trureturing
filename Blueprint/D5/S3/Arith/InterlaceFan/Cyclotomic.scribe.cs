using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.InterlaceFan;

internal sealed class CyclotomicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclotomic propagation and rational witnesses for interlace certificates.",
        H("Rational values and root orders"), Blocks(
            Describe.Lean(DescribeId.Create("interlace-cosine-evaluation"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval"),
                H("Cosine evaluation of an interlace functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reciprocal-pair evaluation is twice the cosine sum. The interlace functional is its negative half."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-polynomial-evaluation"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval_poly"),
                H("Evaluation of the reciprocal polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every certificate index, evaluation at the corresponding standard root of unity equals the real cosine sum. Each coordinate contributes the two monomials with exponents k and n-k. At the middle index for even n these coincide, giving twice the coordinate as the polynomial coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-rational-propagation"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.rational_const_on_orderClass"),
                H("Rational values propagate through an order class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For rational coordinates and a positive darga n, a rational certificate value at one primitive d-th root is the same at every certificate root of order d, where d divides n. Multiplying the certificate value by minus two gives the rational polynomial value. Subtracting that constant gives a polynomial divisible by the d-th cyclotomic polynomial, the minimal polynomial of a primitive d-th root."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-rational-witness"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.rational_witness"),
                H("Rational coordinates realizing an order indicator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every divisor d of n with n at least two, rational sigma coordinates realize the values obtained by subtracting n times the order-class indicator from the totient of d and dividing by two. The coordinates are Ramanujan sums, with the middle coordinate halved when n is even. The public divisor-sum identity proves integrality by induction on the modulus. Finite geometric sums then give the full Fourier transform: n on primitive roots of order d and zero elsewhere. Removing the constant coefficient subtracts the totient of d. Coefficient reconstruction pairs reciprocal exponents and accounts for the doubled middle monomial."))),
                DescribeRole.Theorem))));
}
