// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction;

internal sealed class P48pDerivedActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pDerivedAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational derived action for P48p gives charge inversion and fixed rank sixteen for each member of a pure cubic coset.",
        H("Charge Inversion and Cubic Ranks from the P48p Derived Action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48p-derived-action-charge-inversion-and-cubic-rank"),
                DeclarationHandle.Create(Prefix + "p48p_derived_action_charge_inversion_and_cubic_rank"),
                H("Charge inversion and real fixed rank sixteen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let H act faithfully on the integral charges of a rank-48 lattice D. "
                        + "Let N be the pure factor inside a subgroup L of H, with an embedding of N into SL2(23). "
                        + "Assume L acts irreducibly on the rational charge coordinates and that its action agrees "
                        + "with the charge action on integral vectors. Assume s is an involution in N that is central "
                        + "in L and maps to negative identity under the embedding. Assume c is central in L, has "
                        + "order three, and lies outside N. These hypotheses express the relevant data of the "
                        + "SL2(23) times C3 action in Nebe, arXiv:1212.0865, Theorem 3.6, proof (B). "
                        + "The order-three elements of L are assumed to have real Cartan fixed rank zero or sixteen, "
                        + "the P48p cases of Proposition 4.8.")),
                    Paragraph(Text("Agreement on integral vectors and faithfulness on the charges give faithfulness "
                        + "of the rational action. If S and C denote the rational operators of s and c, their fixed "
                        + "kernels are invariant by centrality and proper by faithfulness. Irreducibility makes "
                        + "both kernels zero. Applying injectivity of S-I and C-I to the factorizations of "
                        + "S squared minus I and C cubed minus I gives S=-I and I+C+C squared=0. Restriction to the "
                        + "integral coordinates gives charge inversion for the unique element mapping to negative identity.")),
                    Paragraph(Text("For each order-three a in N, the elements a, ac, and ac squared have order "
                        + "three. Centrality gives their cube identities, and neither c nor its square belongs "
                        + "to N. Extending the rational matrix of each fixed-space equation to the reals preserves "
                        + "matrix rank. Rank-nullity identifies the rational and real fixed dimensions. "
                        + "The existing cubic rank theorem now makes all three dimensions sixteen.")),
                    Paragraph(Text("Taking the coset member a supplies the real cubic rank hypothesis and the "
                        + "nonzero and proper fixed-space conditions for the order-three case of P48pExtension. "
                        + "The fixed-space conditions for orders eleven and twenty-three, and the comparison of the "
                        + "ambient associator with the type-one cyclic carry class, are separate inputs to that theorem."))),
                DescribeRole.Theorem))));
}
