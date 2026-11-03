using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorThreeFieldBalancedTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldBalancedTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual balanced three-field transport", H("Actual balanced three-field transport"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorthreefieldbalancedtransport-actual-three-field-balanced-transport"),
                DeclarationHandle.Create(Prefix + "actual_three_field_balanced_transport"),
                H("Balanced transport with the original witnesses"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data, charges and oscillator descendants, k is chosen before δ,w. The actual raw-inner supplier is obtained once. The original a,P, canonical truncations, all six signed product laws, and the old cleared, polynomial-action and finite raw-inner reconstruction facts are carried unchanged. The new actual balanced channel under the literal substituted clearing equals signedExtend of the same generally infinite P at the lawful native [s+x,x,z] substitution. The coupled second Jacobi term vanishes using original u/t locality and u-on-w truncation. Original v/t locality and v-on-w truncation give the lower second-coordinate support needed for the signed collision theorem. Independently, canonical truncation of u on v gives a uniform lower s bound and canonical truncation of t on w gives a uniform lower z bound, both uniform in x; no uniform x bound is asserted. All signed targets, zero series, repeated charges, rank zero and indefinite data remain in scope. There is no finite-P, domain, positivity, energy or charge restriction. Only these two charts share witnesses by construction. No raw balanced inverse, unrestricted raw substitution, five-tree common P, pentagon, coherence, analytic convergence or physical realization is claimed. Suppliers retain their original attributions and normalization."))), DescribeRole.Theorem))));
}
