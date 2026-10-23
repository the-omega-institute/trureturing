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
                    Paragraph(Text("The local A/B readouts in both spectator positions are the two remaining Hahn coefficients of the complete binary rational G. This gives the actual finite nested readout at the unchanged P,K, including K=0, empty supports and negative homogeneous degrees. Independent genuine outer locality, joint outer support, the finite antidiagonal reindexing and the final middle Taylor equality are further obligations.")),
                    Paragraph(Text("The Reg source reconstructs the complete dependent telescope. Four-slot registration remains unfinished under issue #20163 because whole-family variation, sensitivity, observational dependence and the final sourceSelection/escapeFrom evidence are absent. No declared_validated status is asserted."))),
                DescribeRole.Theorem))));
}
