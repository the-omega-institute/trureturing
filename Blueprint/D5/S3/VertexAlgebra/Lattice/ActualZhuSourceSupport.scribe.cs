using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuSourceSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuSourceSupport", H("Literal lattice Zhu source relations"), Blocks(
            Paragraph(Text("The native carrier is the complete finite-support sum over integral lattice charges of the complex oscillator polynomial algebra. O is the original literal span of circles with unrestricted second state. Positive definiteness is the sole extra lattice hypothesis for quotient multiplication. No restriction to nonzero rank, nonzero charge, a preferred dual class or a unique minimum is imposed.")),
            Paragraph(Text("Mature source: Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, arXiv q-alg/9605032v1, Theorem 3.4 and Remark 2.11. The native star coefficient is choose(m,i). Native field, mixed-commutator, creation, translation and energy suppliers are reused. This implementation supplies algebraic source relations; it does not establish the full finite transition span, the sharp sum of squared bottom dimensions, joint faithfulness, CFT, fusion, anomaly or string-theory completion.")),
            Describe.Lean(
                DescribeId.Create("actualzhusourcesupport-ground-right-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceSupport.ground_right_support"), H("Charged right support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("E_delta times (H_delta+k_delta) vanishes in the literal quotient, using ground translation and all-charge right-current transport."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhusourcesupport-ground-left-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuSourceSupport.ground_left_support"), H("Charged left support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ground commutator converts right support into (H_delta-k_delta) times E_delta equal to zero."))), DescribeRole.Theorem))));
}
