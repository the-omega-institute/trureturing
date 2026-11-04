using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFourFieldRawMiddleCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldRawMiddleCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("LatticeSectorFourFieldRawMiddleCoefficients", H("LatticeSectorFourFieldRawMiddleCoefficients"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorfourfieldrawmiddlecoefficients-actual-four-field-raw-middle-coefficients"), DeclarationHandle.Create(Prefix + "actual_four_field_raw_middle_coefficients"),
                H("Actual four-field middle reconstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, four labelled charges alpha,beta,gamma,eta and descendants u,v,t,q, one k is chosen from all six pair localities before delta,w. The same a,P, all four original canonical-on-w truncations, all twenty-four signed labelled product laws, previous actual inner action and actual middle Rmid action are retained. At every signed [x,b,z,y], the actual channel u_x((v_b t)_z(q_y w)) equals the explicit finite seven-index readout of the same native numerator N=P[X0,X1+X2,X2,X3]. Every mode is minus its coordinate minus one. The charges are alpha acting on (beta+gamma)+(eta+delta), beta+gamma acting on eta+delta, beta acting on gamma, and eta acting on delta. Actual b support is derived from canonical v-on-t truncation; y support uses the original q-on-w bound; z support at fixed b,y is derived from canonical truncation of the actual fused state on the actual q-mode input, uniformly in outer x. Literal supported injectivity identifies the actual channel with the proved native inverse. No independent witnesses, enlarged k or a, extra cutoff, weak associativity, finite P, Gram, domain, energy, positivity or charge restriction is assumed. Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution remains in the preceding constructions. Five-tree coherence, pentagon, sewing, analytic or physical realization and full string theory remain outside the conclusion."))), DescribeRole.Theorem))));
}
