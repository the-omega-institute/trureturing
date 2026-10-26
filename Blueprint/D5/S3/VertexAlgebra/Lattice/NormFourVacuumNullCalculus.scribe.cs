using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourVacuumNullCalculusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private production coefficient calculus for the norm-four vacuum relation.",
        H("Creation, Current and Transport Calculus"),
        Blocks(
            Paragraph(Text("This module contains the private coefficient calculus consumed by NormFourVacuumNull. "
                + "Its oscillator P(r) is the actual sum of a_i X(i,r) in the lattice oscillator algebra. "
                + "The directional partial derivatives and current actions are evaluated on actual "
                + "finite-support charge states.")),
            Paragraph(Text("The actual creation recurrence determines the coefficients through degree six "
                + "after multiplication by 720. Charge transport of the eight required oscillator monomials "
                + "gives finite annihilation coefficients. Current annihilation bounds justify replacing "
                + "both unbounded normal-ordering sums by their finite supports. These identities yield "
                + "the scaled production mode action on each required atom, including the actual negative "
                + "creation-index convention.")),
            Paragraph(Text("The phase identities use only the integral cocycle and the norm-four condition. "
                + "All declarations remain private helpers; the sole public level-six vacuum null theorem "
                + "and its concrete atom evaluations and descendant cancellations are in NormFourVacuumNull. "
                + "The imported lattice-field and norm-four-vector sources retain the attribution given there.")))));
}
