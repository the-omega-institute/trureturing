using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuCurrentRelationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuCurrentRelations", H("Literal lattice Zhu source relations"), Blocks(
            Paragraph(Text("The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.")),
            Paragraph(Text("Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11, supply the classical lattice Zhu framework. The native fields, grading, creation and translation retain their original definitions. The quotient product and literal circle relations use the original binomial coefficient choose(m,i).")),
            Paragraph(Text("ActualZhuCurrentNormalForm, the native creation derivative and ground-product coefficients identify full opposite-charge circles with falling-factorial current polynomials. ActualZhuSourceProjectors applies the resulting relation for every integral alpha to eliminate grid weights violating a lattice inequality.")),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentrelations-single-weighted-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.single_weighted_grade"), H("Weighted energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weighted oscillator homogeneity gives the exact original charge-plus-oscillator grade."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentrelations-hcharge"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.Hcharge"), H("Charge-linear current"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("H_alpha is the sum of alpha_i H_i; this includes rank zero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentrelations-creation-class-recurrence"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_recurrence"), H("Neutral creation recurrence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translation of the original creation coefficient and its exact energy give (n+1) C_(n+1)=(H_alpha-n) C_n in the literal quotient. The original creation_derivation proof is reused."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentrelations-creation-class-choose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.creation_class_choose"), H("Falling-factorial coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The neutral creation coefficient class is Ring.choose(H_alpha,n), by the exact recurrence and initial value."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentrelations-opposite-circle-sum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.opposite_circle_sum"), H("Full opposite-charge circle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original ground_product supplier evaluates the literal circle of e_alpha with e_(-alpha), retaining all choose(k,j) terms."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentrelations-current-choose-relation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.current_choose_relation"), H("Chu-Vandermonde relation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete opposite-circle sum is Ring.choose(k+H_alpha,2k+1), which vanishes in the source quotient."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhucurrentrelations-all-alpha-current-relation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuCurrentRelations.all_alpha_current_relation"), H("All-alpha squarefree current polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every alpha, the ordered product over j=0,...,2k of H_alpha+k-j vanishes, where k is its nonnegative charge energy. The factors have the distinct integer roots -k,...,k. Alpha zero and rank zero are included; rationality and semisimplicity are not assumed."))), DescribeRole.Theorem))));
}
