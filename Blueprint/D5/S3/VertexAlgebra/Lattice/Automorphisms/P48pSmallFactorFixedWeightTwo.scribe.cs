// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Automorphisms;

internal sealed class P48pSmallFactorFixedWeightTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Automorphisms/P48pSmallFactorFixedWeightTwo.";
    private static readonly LibraryNoteRef LatticeSource =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The small-factor bounds in the P48p analysis force two independent fixed states of actual conformal weight two.",
        H("Fixed Weight-Two States under the P48p Small-Factor Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48p-small-factor-fixed-weight-two"),
                DeclarationHandle.Create(Prefix + "p48p_small_factor_fixed_weight_two"),
                H("Two independent fixed states for the small-factor case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LatticeSource),
                Blocks(
                    Paragraph(Text("Let D have rank 48 and a positive-definite real Gram matrix. The finite group H has a subgroup K of order at most 16 with index dividing 12 and acts on the integral charges by bilinear isometries. A group E acts on the actual carrier by complex linear equivalences preserving every integer vertex mode. Through a homomorphism π from E to H, each e sends the ground state at a to the ground state at the charge prescribed by π(e), multiplied by a unit depending on e and a.")),
                    Paragraph(Text("The real irreducible degree bound for the small-factor case gives a proper nonzero invariant subspace in the real Cartan representation of H. Pulling the action back along π gives the invariant subspace required for the Gram projector construction. The theorem gives a complex matrix C with C gramComplex(D) = 1 and a pair of complex-linearly independent states in grade two. Both states are fixed by every e, and mode one of the field of omega(D,C) acts on each by the scalar two."))),
                DescribeRole.Theorem))));
}
