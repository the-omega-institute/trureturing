using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class ChargedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original oscillator and literal Leech tensor charged coefficients have exact BPZ adjoints.",
        H("Charged Complex-Bilinear BPZ Adjoints"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("oscillatorchargedtranspose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Charged.oscillator_charged_transpose"),
                H("Finite Integer Laurent Transpose"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every original oscillatorCoefficient at exponent e transposes to the coefficient at exponent -2 times chargeNorm minus e, with the same charge. Its defining sum is supported in the actual translated polynomial support. Creation multiplication transpose expands the paired coefficient into a finite double sum on the two original polynomial supports.")),
                    Paragraph(Text("The nonzero diagonal has integer indices satisfying secondDegree = e + chargeNorm + firstDegree. Equivalently firstDegree = -2 times chargeNorm - e + chargeNorm + secondDegree. Interchanging the finite sums therefore gives the reflected exponent, including every negative-index zero case. No infinite-support sum is exchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensorchargedadjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Charged.tensor_charged_adjoint"),
                H("Original Chosen-Ground Tensor Adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The tensor result uses literal GolayLeech data and the original nested chosen twisted ground. NativeSymmetricForm.original_integral_adjoint supplies its ground factor: exactly one epsilon(charge,-charge), acting on groundAction(-charge). The oscillator factor retains the same charge, and chargeScalar appears exactly once outside the bilinear pairing. Tensor induction proves the identity for arbitrary ActualTensor states, not only pure tensors.")),
                    Paragraph(Text("These identities do not prove all-state field invariance, twisted Jacobi, twisted-sector gluing, Monster symmetry, fusion, string theory, or AdS/CFT. Those conclusions require their own original field bridges. No positivity, unitary pairing, substitute ground, or desired transpose is assumed."))),
                DescribeRole.Theorem))));
}
