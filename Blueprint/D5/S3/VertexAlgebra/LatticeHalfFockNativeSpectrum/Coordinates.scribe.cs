using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum;

internal sealed class CoordinatesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native half-oscillator spectral coordinates",
        H("All states of the original tensor carrier"),
        Blocks(
            Paragraph(Text("The state space is the original polynomial oscillator tensor the original chosen finite ground representation. TensorProduct.equivFinsuppOfBasisLeft supplies its actual occupation coefficients. Its inverse is the finite sum of monomial(d,1) tensor the ground-valued coefficient at d; both inverse identities belong to this linear equivalence. There is no finite replacement carrier or occupation cutoff.")),
            Describe.Lean(
                DescribeId.Create("native-half-fock-coefficient-diagonalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Coordinates.coefficient_diagonalization"),
                H("Every-state original L0 diagonalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Assume both H times gramComplex equals one and gramComplex times H equals one. For every original tensor state and every unrestricted finite occupation d, the coefficient of original tensorL at mode zero is multiplied by rank/16 plus W(d)/2, where W(d) is the sum of d(i,m)(2m+1). The actual inverse finite expansion and linearity extend the original monomial identity to every state."))),
                DescribeRole.Theorem),
            Paragraph(Text("eigen_support_iff identifies each complex eigenspace exactly: a state has eigenvalue lambda precisely when every occupation with a different spectral value has zero ground coefficient. Nonzero complex scalars act injectively on the actual ground space. No Gram positivity, energy assumption on the lattice charges, or assumed state-field law is used.")),
            Paragraph(Text("The rank/16 shift is unchanged. The original Ytw_omega comparison is a separate conformal interface; these spectral results use the literal tensorL and do not replace that field identification. Full twisted Jacobi, orbifold gluing, the Monster, fusion, anomalies, string dynamics and AdS/CFT are not conclusions of this construction.")))));
}
