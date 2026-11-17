using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuOscillatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuOscillator", H("Literal lattice Zhu source relations"), Blocks(
            Paragraph(Text("The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.")),
            Paragraph(Text("Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).")),
            Paragraph(Text("ActualZhuGroundCurrent and ActualZhuProduct supply the current grade and complete higher circles. Their fixed-numerator Pascal rows reduce every negative current to mode minus one in the literal quotient. ActualZhuCurrentNormalForm uses this reduction for arbitrary oscillator tails.")),
            Describe.Lean(
                DescribeId.Create("actualzhuoscillator-current-higher-circle"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_higherCircle"), H("Complete higher-circle row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weight-one higher circle is the full Pascal sum of fixed-numerator neighboring negative-current rows, with no omitted binomial terms."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhuoscillator-current-pair-mem-zhu-o"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.current_pair_mem_zhuO"), H("Triangular fixed-numerator elimination"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strong induction separates the leading fixed-numerator row from the complete higher circle; every remaining row has a strictly smaller index."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhuoscillator-negative-current-class"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.negative_current_class"), H("Physical negative-current reduction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original state v, pi(h_i(-n-1)v)=(-1)^n pi(h_i(-1)v)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhuoscillator-oscillator-variable-class"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator.oscillator_variable_class"), H("Arbitrary oscillator tails"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reduction applies to single(delta,X(i,n)p) for every charge and oscillator polynomial, including the zero polynomial."))), DescribeRole.Theorem))));
}
