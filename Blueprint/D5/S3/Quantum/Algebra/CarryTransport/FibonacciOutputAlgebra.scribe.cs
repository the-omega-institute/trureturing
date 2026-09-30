using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CarryTransport;

internal sealed class FibonacciOutputAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Fibonacci carry unitary has precisely the conjugated two-sector algebra as its maximal one-step low-output algebra.",
        H("Fibonacci carry output algebra"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-carry-output-algebra"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/CarryTransport/FibonacciOutputAlgebra.result"),
            H("Maximal one-step low-output algebra"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every natural d,e at least two, A=(Z/dZ)^2 and H=(Z/eZ)^2 carry their canonical residue labels. The Hilbert spaces are the Euclidean complex coordinate spaces. The Fibonacci permutation sends (x0,x1) to (x1,x0+x1); U is the modulus-de permutation transported through the specified coordinate identification x=a+d*h. Its derived action sends (a,h) to (f(a),(h1,h0+h1+k(a))), where k(a)=(a0.val+a1.val)/d.")),
                Paragraph(Text("Define Dout by the actual Heisenberg pullback of B tensor I belonging to the low tensor range. Then Dout equals the low-Fibonacci conjugate of the direct product of the full matrix algebras on the two actual carry fibers. Alpha is exactly Ud-adjoint times B times Ud. Every member has pullback alpha(B) tensor I. For arbitrary complex B, membership is equivalent to the existence of a complex-valued function of the actual low density marginal giving the output expectation for every positive trace-one joint input.")),
                Paragraph(Text("The carry-sector Hilbert spans have complex dimensions d(d+1)/2 and d(d-1)/2. The operator-defined Dout has complex dimension d^2(d^2+1)/2, and its actual self-adjoint subspace has the same real dimension.")),
                Paragraph(Text("The classification follows from high-label collisions for opposite carries. Half-rank-one correlated density states with phases 1 and i give equal low marginals and separate every excluded complex coefficient. Restricted Euclidean basis spans, a full-block algebra equivalence, and the real/imaginary decomposition of the actual output algebra establish the dimensions."))),
            DescribeRole.Theorem))));
}
