using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuMinimum", H("Native weights and tied minima"), Blocks(
            Paragraph(Text("The carrier and literal circle span are unchanged. The lattice is arbitrary positive-definite integral even, including rank zero and zero charge. Mature source: Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, https://arxiv.org/html/q-alg/9605032v1, Theorem 3.4 and Remark 2.11. Native energy, oscillator, source support and inverse Gram suppliers are reused. Lagrange interpolation is supplied by pinned Mathlib under Apache-2.0. These are components of the finite source-span and joint-faithfulness consumer; no independent mathematical novelty or physical completion is asserted.")),
            Describe.Lean(
                DescribeId.Create("actualzhuminimum-minimum-iff-all-alpha"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuMinimum.minimum_iff_allAlpha"), H("All lattice inequalities and global minima"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The change of the original rational charge energy under gamma plus alpha is energy(alpha) plus the integral pairing with beta plus G gamma. Applying it to both alpha and minus alpha identifies all global minima, including ties, with the full family of source inequalities."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhuminimum-survivor-minimum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuMinimum.survivor_minimum"), H("Every surviving source weight has a native minimum label"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing inverse Gram and discriminant coset equivalence send every integral source weight satisfying all alpha inequalities to its dual class and a charge in the full attained-minimum equality fiber. No positive-rank or uniqueness assumption is used."))), DescribeRole.Theorem))));
}
