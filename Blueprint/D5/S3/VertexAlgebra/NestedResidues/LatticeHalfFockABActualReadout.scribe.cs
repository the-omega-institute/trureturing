using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class LatticeHalfFockABActualReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite source/source nested Q products at the original homogeneous numerator.",
        H("Actual A/B nested extraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-ab-nested-readout"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_nested_readout"),
                H("Independent finite inner cutoff and the original rational numerator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("Keep the original labels y=J, v=A and z=B. For arbitrary actual states a,b, tensor x, linear covector phi and signed gamma,delta,d,r,n,j, let P satisfy the actual homogeneous numerator equation at the supplied cutoff K. The inner A/B cutoff I and outer cutoff H are independent natural numbers. The theorem identifies the actual coefficient of Q_(d-j)^1(J,Q_(r+j)^gamma(A,B;I);H) with the supported outer readout of completeAB(gamma,r+j,I,P/Q_K). In particular I=K retains the actual original finite field. Neither K nor I is assumed to be a locality order.")),
                    Paragraph(Text("The actual finite Laurent supplier provides a numerator P0 at its own order K0. The homogeneous quotient comparison identifies P/Q_K with P0/Q_K0. Each nested summand has total mode degree (r+j)+(d-j)+n=d+r+n, so the supplier identifies all six words on exactly the required degree slice. The existing nested supported extraction applies with independent I; it does not compare actual fields at I and K0. The complete intermediate field supplies outer support, while the actual rightmost input supplies inner support.")),
                    Paragraph(Text("The local A/B readouts in both spectator positions are the two remaining Hahn coefficients of the complete binary rational G. This gives the actual finite nested readout at the unchanged P,K, including K=0, empty supports and negative homogeneous degrees. The complete-field joint outer support and finite antidiagonal theorem below consumes this identification. Evaluation of its complete outer residues and the final middle Taylor equality remain further obligations.")),
                    Paragraph(Text("The Reg source reconstructs the complete dependent telescope. Four-slot registration remains unfinished under issue #20163 because whole-family variation, sensitivity, observational dependence and the final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-ab-joint-outer-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout.actual_ab_joint_outer_support"),
                H("Complete joint outer support and a finite antidiagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For the original actual middle family, put N=((K:Z)-r).toNat and B(j)=((H(j):Z)-(d-j)).toNat. Each H(j) is an independent genuine locality order for the complete fields J and Q_(r+j)^gamma(A,B;K). The theorem bounds the support of the complete ordinary outer residue by ell<B(j), and every larger fractional cutoff computes the same complete outer readout. The original numerator P,K and actual finite inner cutoff K are retained.")),
                    Paragraph(Text("The degree-preserving shift d to d+ell and n to n-ell identifies the complete residue with the same original homogeneous slice. Complete-field locality then annihilates the tail; neither individual ordered half is asserted to vanish. With T=N+sum_(j<N) B(j), the finite map (j,ell) to (j+ell,j) is a bijection onto the supported antidiagonal indices. Thus the weighted sum of actual nested coefficients equals the finite sum over t<T and j<=t,j<N of chooseSign(d,j) choose(-1/2,t-j) times the complete outer residue at ell=t-j. Zero and empty ranges remain in scope.")),
                    Paragraph(Text("The complete outer residues in this antidiagonal still require evaluation in the binary Laurent rational G before finite_forward_outer_taylor gives the original middle Taylor equality. The theorem supplies actual identification, genuine joint support and finite reindexing; it does not assert that remaining evaluation or the full middle equality. The faithful Reg source reconstruction retains the entire independent locality family; the four-slot audit remains unfinished under issue #20163."))),
                DescribeRole.Theorem))));
}
