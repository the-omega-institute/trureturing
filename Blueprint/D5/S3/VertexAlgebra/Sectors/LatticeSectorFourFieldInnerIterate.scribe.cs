using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFourFieldInnerIterateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldInnerIterate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual four-field inner transport", H("Actual four-field inner transport"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorfourfieldinneriterate-actual-four-field-inner-iterate-transport"),
                DeclarationHandle.Create(Prefix + "actual_four_field_inner_iterate_transport"),
                H("Actual four-field inner transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, four charges and oscillator descendants, choose one locality order from all six pairs before the fifth charge and state. The same original four canonical-on-input truncation bounds and generally infinite numerator P retain all twenty-four labelled product laws. At every signed four-index, literal finite polynomial action by R on the actual channel u_x(v_y((t_b q)_z w)) equals the signed native power series P(x,y,b+z,z). Here R is x^a0 y^a1 (b+z)^a2 z^a3 (x-y)^k (x-b-z)^k (x-z)^k (y-b-z)^k (y-z)^k b^k. The finite five-index cross expansion precedes the original charged t,q,w Borcherds reconstruction, and both outer canonical modes are linear readouts. Original q-on-w truncation bounds every residue fiber uniformly in both spectator modes. The residue binomial choose(k-e2-1,i) is independent of all five cross indices; only finite sums are exchanged. Signed bivariate cancellation on a fixed native slice identifies exactly the original P. No cutoff on a varying intermediate state, enlarged original locality or monomial bound, finite numerator, rank, Gram, energy, positivity or charge restriction occurs. This is one algebraic inner collision; no coherence, sewing, analytic convergence or physical realization follows. Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions are preserved."))), DescribeRole.Theorem))));
}
