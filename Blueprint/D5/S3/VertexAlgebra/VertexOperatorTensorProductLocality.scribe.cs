using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class VertexOperatorTensorProductLocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/VertexOperatorTensorProductLocality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nested coefficient bounds for scalar-signed tensor locality.",
        H("Signed Tensor Locality"),
        Blocks(
            Paragraph(Text("The signed discrepancy is A_p C_q minus s C_q A_p. "
                + "Polynomial clearing acts by the coefficient shift f(p+1,q)-f(p,q+1). "
                + "Ordered products have a uniform upper bound on the inner field "
                + "index, and a separate outer-mode bound for each inner coefficient. "
                + "Reversed products have the opposite orientation. The actual nested "
                + "tensor action uses compatible orientations, not an unbounded mixed "
                + "product. All summation is pointwise on the input vectors.")),
            Paragraph(Text("Independent input-field locality is a legitimate premise. "
                + "The scalar exchange sign is not silently replaced by an ordinary "
                + "commutator. For the intended even matter factor its sign is one; "
                + "the bc factor can have sign minus one. No generic super tensor "
                + "state-field algebra is asserted without the Koszul crossing rule.")),
            Describe.Lean(
                DescribeId.Create("nested-finite-support"),
                DeclarationHandle.Create(Prefix + "convolution_finite"),
                H("The two-index diagonal has finite support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inner indices form a finite interval from "
                    + "the two uniform inner-field bounds. For each such index the "
                    + "outer indices lie in a second finite interval. A finite union "
                    + "of these intervals controls the nested coefficient sum. "
                    + "Reversal uses the proved coordinate-swap bijection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clearing-polynomial-transfer"),
                DeclarationHandle.Create(Prefix + "convolution_delta_left"),
                H("Clearing shifts transfer through the diagonal convolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integer bijections reindex each shift. "
                    + "Finite support of both shifted summands justifies subtraction "
                    + "of the finsums. This is an actual coefficient identity, "
                    + "not an interface assuming tensor locality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-tensor-locality"),
                DeclarationHandle.Create(Prefix + "signedLocal_tensor"),
                H("The product exchange sign and the sum of clearing orders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the U fields have scalar-signed locality "
                    + "with sign s and order N, and the V fields have sign t and "
                    + "order M, their tensor fields have sign s times t and order "
                    + "N plus M. Both ordered actions are identified with actual "
                    + "finite nested convolutions. Clearing powers transfer to the "
                    + "two factors, the factor identities are applied, and tensor "
                    + "induction extends the equality to all vectors. The argument "
                    + "works for arbitrary complex scalars; no use of s squared "
                    + "or t squared equal to one is required."))),
                DescribeRole.Theorem))));
}
