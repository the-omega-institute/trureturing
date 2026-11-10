using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuSourceProjectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuSourceProjectors", H("Finite projectors inside the literal source quotient"), Blocks(
            Paragraph(Text("The carrier and literal circle span are unchanged. The lattice is arbitrary positive-definite integral even, including rank zero and zero charge. Mature source: Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, https://arxiv.org/html/q-alg/9605032v1, Theorem 3.4 and Remark 2.11. Native energy, oscillator, source support and inverse Gram suppliers are reused. Lagrange interpolation is supplied by pinned Mathlib under Apache-2.0. These are components of the finite source-span and joint-faithfulness consumer; no independent mathematical novelty or physical completion is asserted.")),
            Describe.Lean(
                DescribeId.Create("actualzhusourceprojectors-coordinate-sum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_sum"), H("Coordinate interpolation partitions the unit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For coordinate i the native all-alpha relation supplies the nodal polynomial with integer roots from minus k_i through k_i. Pinned Mathlib Lagrange basis polynomials, evaluated in the commutative current subalgebra, sum to one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhusourceprojectors-coordinate-eigen"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.coordinate_eigen"), H("Coordinate eigenvalue identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by H_i on each coordinate Lagrange factor is its integer node times that factor, because the remaining nodal term vanishes in the literal quotient."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhusourceprojectors-projector-sum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_sum"), H("Joint sum-one decomposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Taking products over all coordinates and summing over the finite dependent grid gives the source unit, including the empty coordinate product in rank zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhusourceprojectors-projector-eigen"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_eigen"), H("Joint current eigenvalues"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every H_i acts on a joint source projector by its corresponding grid weight."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhusourceprojectors-projector-survives"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.projector_survives"), H("All-alpha elimination"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply each native alpha annihilator by a joint projector. A nonzero projector forces one complex scalar factor to vanish, hence the integral weight lies between minus energy(alpha) and energy(alpha). The entire family of alpha inequalities is used; coordinate bounds alone are not substituted."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhusourceprojectors-current-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors.current_scalar"), H("Scalar action of the full current subalgebra"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Adjoin induction on actual current generators, scalars, sums and products shows that every current-algebra element acts by a scalar on each joint projector. The ambient Zhu algebra is never assumed commutative."))), DescribeRole.Theorem))));
}
