using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuCurrentNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuCurrentNormalForm", H("Literal lattice Zhu source relations"), Blocks(
            Paragraph(Text("The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.")),
            Paragraph(Text("Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).")),
            Paragraph(Text("ActualZhuAlgebra supplies associativity on the original quotient. ActualZhuGroundCurrent and ActualZhuOscillator supply the ground and higher-mode current identities. The resulting all-charge polynomial normal form is used by ActualZhuCurrentRelations and ActualZhuTransitionSpan to span the source quotient before applying any representation.")),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-h"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.H"), H("Neutral current class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The class of the original current state in the full literal Zhu quotient."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-e"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.E"), H("Charged ground class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The class of single(delta,1) for every integral charge."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-oscillator-left-current"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_left_current"), H("Native left action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The left current subtracts the charge pairing when expressed as insertion of X(i,0)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-oscillator-right-current"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_right_current"), H("All-charge right-current transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Polynomial induction extends the direct ground right-current law to every oscillator tail using associativity and negative-current reduction, without a generic skew tower."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-currents-commute"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currents_commute"), H("Neutral currents commute"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The neutral specialization of right-current transport identifies both orders with the same oscillator product."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-current-algebra"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentAlgebra"), H("Current subalgebra"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C is Algebra.adjoin over the complex numbers of the range of H. Only this subalgebra is given a commutative ring structure; Q remains possibly noncommutative."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-current-generator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.currentGenerator"), H("Generator inside C"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each H_i is regarded as an element of the generated current subalgebra."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-oscillator-evaluation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillatorEvaluation"), H("Physical polynomial evaluation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex algebra map from the original oscillator polynomials to C sends X(i,n) to (-1)^n H_i."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentnormalform-oscillator-normal-form"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentNormalForm.oscillator_normal_form"), H("Literal all-charge oscillator normal form"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every delta and p, pi(single(delta,p))=E_delta times oscillatorEvaluation(p). Equality is in the original source quotient, with no bottom-action kernel replacement."))), DescribeRole.Theorem))));
}
