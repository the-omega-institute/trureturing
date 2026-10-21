using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.InterlaceFan;

internal sealed class CyclotomicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclotomic propagation and Ramanujan witnesses for interlace certificates.",
        H("Order classes and rational values"), Blocks(
            Describe.Lean(DescribeId.Create("interlace-cosine-evaluation"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.I_eq_eval"),
                H("Cosine evaluation of an interlace functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real evaluation of the reciprocal pair of monomials at a certificate root is twice the cosine sum in the sigma coordinates. The interlace functional is its negative half."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-order-class-propagation"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.const_on_orderClass"),
                H("Propagation within an order class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a rational polynomial evaluation is invariant between two certificate indices of the same root order, equality of one interlace value propagates to every index in that order class."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-ramanujan-witness"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.witness"),
                H("Ramanujan divisor witness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive modulus, the normalized sum of Ramanujan phases over its divisors is the indicator of divisibility. This identity supplies the arithmetic witness values used by the interlace construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-witness-values"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Cyclotomic.witness_values"),
                H("Rational order-class target values"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a divisor of n, the order-class indicator determines a rational target value for every certificate index. These targets are the data passed to Fourier inversion."))),
                DescribeRole.Theorem))));
}

