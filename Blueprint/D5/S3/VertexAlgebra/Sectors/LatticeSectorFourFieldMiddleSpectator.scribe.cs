using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFourFieldMiddleSpectatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldMiddleSpectator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual middle spectator transport", H("Actual middle spectator transport"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorfourfieldmiddlespectator-actual-four-field-middle-spectator-transport"),
                DeclarationHandle.Create(Prefix + "actual_four_field_middle_spectator_transport"),
                H("Two actual channels with the same numerator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, four labelled charges alpha,beta,gamma,eta and oscillator descendants u,v,t,q, one locality order k is chosen from all six original pairs before the arbitrary fifth charge delta and state w. The same original bounds a and generally infinite four-variable numerator P retain all four canonical-on-w truncations, all twenty-four signed labelled product laws and the previous actual inner-channel identity u_x(v_y((t_b q)_z w)) at P(x,y,b+z,z). With these exact witnesses, at every signed e, polynomial action by Rmid on the actual channel u_x((v_b t)_z(q_y w)) equals signedExtend of the native substitution P[X0,X1+X2,X2,X3]. In output coordinates x,b,z,y, Rmid is x^a0 (b+z)^a1 z^a2 y^a3 (x-b-z)^k (x-z)^k (x-y)^k b^k (b+z-y)^k (z-y)^k. The actual outer canonical mode has charge alpha and input charge (beta+gamma)+(eta+delta); the middle mode has charge beta+gamma and input eta+delta; the two inner modes have inputs gamma and delta. Each mode index is minus its coordinate minus one. Three finite spectator expansions use shifted natural bounds a1+p,a2+r,a3+s derived from the original bounds. Original v/q locality supplies the balanced Borcherds reconstruction; original t/q locality and t-on-w truncation make its residue finite before the outer u mode is mapped. Only finite sums are exchanged. The resulting five cross factors are compared with the original product law on the fixed original u,q slice, identifying the same P at x,b+z,z,y for negative as well as nonnegative indices. No independently selected witnesses, enlarged k or a, extra cutoff on q_y w or a fused state, finite numerator, rank, Gram, domain, energy, positivity or charge restriction is assumed. This is an algebraic middle collision together with the previous inner collision; a common identity for all five trees, the pentagon, sewing, analytic convergence, physical realization and full string theory remain outside this conclusion. The original Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions are retained."))), DescribeRole.Theorem))));
}
