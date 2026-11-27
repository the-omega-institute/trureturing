// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction;

internal sealed class P48pDerivedExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pDerivedExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full P48p derived action supplies the projected charge data for the extension obstruction.",
        H("The P48p Extension Obstruction from the Derived Action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48p-associator-extension-obstruction-of-derived-action"),
                DeclarationHandle.Create(Prefix + "p48p_associator_extension_obstruction_of_derived_action"),
                H("The derived action forces weight-two dimension at least two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the finite group A act faithfully by charge isometries on a positive-definite even integral "
                        + "lattice D of rank 48. Let N be a normal subgroup of A whose order divides "
                        + "2^4 * 3 * 11 * 23 and whose index divides 12, with an embedding into SL2(23). "
                        + "A subgroup L containing N acts irreducibly on the rational charge coordinates and "
                        + "agrees with A on integral charges. An involution of N mapping to negative identity "
                        + "is central in L, and L has a central element of order three outside N. The real Cartan "
                        + "fixed ranks in L at order three are zero or sixteen. At orders eleven and twenty-three "
                        + "in N the fixed ranks are eight and four, respectively.")),
                    Paragraph(Text("Let H be the projected charge subgroup of A and let M be the preimage of N "
                        + "under the inclusion of H in A. Then M is normal in H, its index divides the index "
                        + "of N in A, and its order divides the order of N. The inclusion of M into N preserves "
                        + "element orders and gives an embedding of M into SL2(23). The derived action theorem "
                        + "gives charge inversion on elements mapping to negative identity. Taking the member "
                        + "of each pure cubic coset that lies in N gives rank sixteen and a nonzero proper fixed space at "
                        + "order three. At orders eleven and twenty-three, ranks eight and four also give nonzero "
                        + "proper fixed spaces in rank 48.")),
                    Paragraph(Text("A subgroup K of a finite group G projects onto H. The faithful complex linear "
                        + "action of G on the lattice carrier preserves modes on K and maps each ground vector "
                        + "to the ground vector at the projected charge times its complex unit phase. Assume the "
                        + "ambient associator restricts to a two-coboundary on K. For elements of K of ambient and "
                        + "charge order three, fixed rank sixteen, and phase one on fixed charges, assume the "
                        + "ambient cyclic pullback is the type-one carry class up to a two-coboundary, using a "
                        + "complex unit of exact order three.")),
                    Paragraph(Text("The projected data meet the Cartan hypotheses of the associator extension "
                        + "obstruction. With an injective linear inclusion of the K-invariant lattice states "
                        + "that sends grade two to the target's finite-dimensional weight-two eigenspace, "
                        + "the obstruction gives target weight-two dimension at least two."))),
                DescribeRole.Theorem))));
}
