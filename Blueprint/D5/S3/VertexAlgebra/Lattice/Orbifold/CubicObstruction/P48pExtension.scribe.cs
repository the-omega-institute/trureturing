// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction;

internal sealed class P48pExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The P48p Cartan dichotomy gives a weight-two obstruction to an extension that trivializes the ambient associator.",
        H("The P48p Associator Extension Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48p-associator-extension-obstruction"),
                DeclarationHandle.Create(Prefix + "p48p_associator_extension_obstruction"),
                H("At least two independent weight-two states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let D be a positive-definite even integral lattice of rank 48. A finite group G acts faithfully "
                        + "by complex linear equivalences on the actual lattice carrier. Its subgroup K projects "
                        + "surjectively by a group homomorphism to a finite charge group H, with a faithful charge "
                        + "isometry action. The K action preserves the modes and sends each ground vector to the "
                        + "ground vector at the projected charge, scaled by a complex unit.")),
                    Paragraph(Text("Assume H has a normal subgroup N whose order divides 2^4 * 3 * 11 * 23 "
                        + "and whose index divides 12, with an embedding into SL2(23). Every element of N mapping "
                        + "to negative identity acts as negation on charges. The real Cartan fixed spaces for elements "
                        + "of N of order 3, 11, or 23 are nonzero and proper. Those of order 3 have dimension 16. "
                        + "The group and rank premises describe the P48p input from Nebe, arXiv:1212.0865, "
                        + "Theorem 3.6, proof (B), and Proposition 4.8.")),
                    Paragraph(Text("The ambient associator restricts to the coboundary of a two-cochain on K. "
                        + "For each element of K of ambient and charge order three, real Cartan fixed rank 16, and "
                        + "phase one on every fixed charge, assume its cyclic pullback is the type-one carry "
                        + "representative times the coboundary of an explicit two-cochain on the cyclic group. "
                        + "The representative uses a complex unit of exact order three. This comparison takes as "
                        + "input the identification of the actual twisted spectrum with the ambient cyclic class "
                        + "in the convention of Evans and Gannon, arXiv:1804.11145, equations (2.13) and (2.14).")),
                    Paragraph(Text("A proper nonzero invariant real Cartan subspace gives a projector quadratic "
                        + "and an inverse-Gram state, both fixed by K. An injective linear vacuum inclusion carries "
                        + "these grade-two states into the finite-dimensional eigenvalue-two eigenspace of the target "
                        + "weight operator. Their images are independent, so the target weight-two dimension is at least two.")),
                    Paragraph(Text("In the irreducible case, lift the projected cubic and charge inversion to x and s "
                        + "in K. The word z = (x (s x s^(-1)))^2 has order three, projects to the same cubic of fixed "
                        + "real rank 16, and has phase one on each fixed charge. The type comparison rules out z in any "
                        + "subgroup trivializing the ambient associator. Since z belongs to K, this case is impossible."))),
                DescribeRole.Theorem))));
}
