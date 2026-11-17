using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuGroundCurrentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuGroundCurrent", H("Literal lattice Zhu source relations"), Blocks(
            Paragraph(Text("The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.")),
            Paragraph(Text("Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).")),
            Paragraph(Text("ActualZhuProduct and ActualZhuAlgebra supply the original star and quotient product; the native derivative, creation and mixed-current identities compute the ground right-current law. ActualZhuOscillator and ActualZhuCurrentNormalForm use these identities to reduce every oscillator polynomial, and ActualZhuSourceSupport applies the translation relation to charged ground states.")),
            Describe.Lean(
                DescribeId.Create("actualzhugroundcurrent-ground-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_grade"), H("Ground energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every original ground state has its nonnegative integral half-norm energy."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhugroundcurrent-translation-weight-mem-zhu-o"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.translation_weight_mem_zhuO"), H("Translation and weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any homogeneous original state a of natural weight K, T(a)+K a lies in the same literal O."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhugroundcurrent-ground-right-current"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.ground_right_current"), H("Direct ground right-current law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mixed commutator at current mode -1, creation and creativity give E_delta H_i equal to the class of h_i(-1)e_delta. The zero-weight star row is handled separately."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhugroundcurrent-current-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_grade"), H("Current energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original current state is homogeneous of energy one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhugroundcurrent-current-star-single"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuGroundCurrent.current_star_single"), H("Left current on a full sector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every oscillator polynomial p, H_i pi(single(delta,p)) is pi(single(delta,X(i,0)p)) plus B(e_i,delta) pi(single(delta,p))."))), DescribeRole.Theorem))));
}
