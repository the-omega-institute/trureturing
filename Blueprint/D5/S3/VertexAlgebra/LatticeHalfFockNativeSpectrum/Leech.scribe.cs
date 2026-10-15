using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum;

internal sealed class LeechDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal Leech native spectral data",
        H("The original chosen carrier and both inverse equations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("literal-leech-native-spectral-data"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/Leech.explicitLeechSpectrum"),
                H("Constructed native basis and integer-sector equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("LeechData is literally ExplicitLeechLattice.data. Its supplied integral Gram determinant is one, giving hu. Int.cast_det gives complex Gram determinant one. The actual complex nonsingular inverse H satisfies both H times gramComplex equals one and gramComplex times H equals one by the standard matrix inverse identities. These parameters construct the actual weight-two coordinate equivalence, the literal tensor-ground-delta Basis and the all-integer direct-sum equivalence."))),
                DescribeRole.Definition),
            Paragraph(Text("The dimension field is obtained from the actual native basis theorem, using the two original choose_spec layers for the ground dimension. It is 98304 for the original eigenspace, not an arithmetic theorem about a replacement label carrier. The package is an application of the general spectral construction, not an additional claim of mathematical novelty.")),
            Paragraph(Text("The constructor proves every field of LeechNativeSpectrum; none is an assumed module, positivity or Jacobi law. It does not select the separate ground representation hidden inside actual_leech_supplier. Untwisted dimensions, the moonshine coefficient, Monster realization, fusion, anomalies and orbifold gluing are not established by these data.")))));
}
