using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CarryTransport;

internal sealed class FibonacciEndpointAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original integer-quotient carry determines the entire single-endpoint algebra of the native Fibonacci transport, including its complete-period return.",
        H("Fibonacci endpoint carry algebras"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-endpoint-carry-algebra"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/CarryTransport/FibonacciEndpointAlgebra.result"),
            H("Exact endpoint blocks and positive periods"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let d,e be arbitrary natural numbers at least two. The low labels A=(Z/dZ)^2 and high labels H=(Z/eZ)^2 have their canonical nonnegative integer representatives. The source matrix is M=[[0,1],[1,1]]. The low permutation f and high permutation use this same Fibonacci step. The joint permutation U is the modulus-de permutation transported through the coordinatewise digit identification x=a+d*h; no coprimality is required.")),
                Paragraph(Text("For every natural endpoint m, integerEvolution is exactly M to the power m applied to the integer representatives of a. Each coordinate of integerEvolution minus the canonical representative of f to the power m of a is divisible by d. sourceCarry is the original integer quotient of this difference by d, reduced modulo e in each coordinate. Thus it is precisely the cumulative carry c_m, rather than a replacement record. The actual high-fiber permutation sends h to f_e to the power m of h plus c_m(a). Two entire high-fiber permutations are equal if and only if their original carries c_m(a) are equal.")),
                Paragraph(Text("For every complex low matrix B, endpointPullback is exactly the adjoint of U to the power m, times B tensor I, times U to the power m. endpointAlgebra D_m consists of precisely those B whose pullback lies in the full low matrix algebra tensor I. endpointAlpha is exactly the adjoint of U_d to the power m, times B, times U_d to the power m. Its inverse is U_d to the power m, times B, times the adjoint of U_d to the power m.")),
                Paragraph(Text("Membership B in D_m is equivalent to endpointAlpha(B) having zero matrix entries between every pair a,b with c_m(a) unequal to c_m(b). CarryBlocks contains the full complex matrix algebra on each actual fiber of c_m. Its canonical embedding uses the sigma-fiber identification and the full block-diagonal algebra. Indexing every high label retains every nonempty fiber and gives zero-dimensional blocks to empty fibers. D_m is exactly the range of this full block embedding conjugated by U_d to the power m. This proves the direct sum over the image of c_m, including singleton fibers and arbitrary complex operators.")),
                Paragraph(Text("For every m with M to the power m equal to the identity modulo d*e, U to the power m is the identity and D_m is the entire low matrix algebra. Such a positive m exists for every d,e at least two. The family on positive endpoints is not antitone: a complete-period endpoint has the full algebra, while D_1 is proper. The latter obstruction uses actual zero- and one-carry labels (0,0) and (d-1,1), with a matrix coefficient between them.")),
                Paragraph(Text("The integer decomposition evolves the low representative together with the accumulated integer carry and identifies the original quotient before reducing modulo e. The common invertible high evolution makes equality of the quotient carries equivalent to equality of full high-fiber maps. The native matrix entry criterion then selects exactly the full carry blocks. Finite permutation order gives a positive source matrix period. The endpoint statements hold for all m, and in particular for every m at least one; they impose no intermediate-time observations, source reset, control, restriction on a high input, or favorable state."))),
            DescribeRole.Theorem))));
}
