using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum;

internal sealed class WeightTwoDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual native weight-two basis",
        H("Unrestricted classification and original ground coordinates"),
        Blocks(
            Paragraph(Text("For any rank, W(d)=1 if and only if d is single(i,0)1 for a unique colour i. Removing any occupied coordinate leaves a nonnegative weighted remainder; weight one forces mode zero and a zero remainder. This proves the classification for every finite occupation, including the absence of occupations at rank zero.")),
            Paragraph(Text("At rank twenty-four the original spectral value is 3/2+W/2, so weight two is exactly W=1. weightTwoEquiv sends an actual weight-two state to its ground coefficient at single(i,0)1. Its inverse is the sum over colours of X(i,0) tensor the corresponding ground vector. The selected-coordinate law and weight_two_reconstruction prove both inverse formulas on all states.")),
            Describe.Lean(
                DescribeId.Create("native-half-fock-actual-weight-two-basis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/WeightTwo.weightTwoBasis_vector"),
                H("Literal oscillator tensor ground-delta basis vectors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Transporting the coordinate-function basis through groundCoordinateEquiv and weightTwoEquiv gives a genuine Module.Basis of the original weight-two submodule. Its vector at (i,t) is exactly X(i,0) tensor Pi.single(t,1). The Basis object proves spanning and linear independence, rather than assigning a dimension to a finite label carrier."))),
                DescribeRole.Theorem),
            Paragraph(Text("chosen_ground4096 consumes the two choose_spec layers of actual_twisted_ground_representation used by the original groundRank and groundRepresentation. The literal ActualGround has dimension 4096 at rank twenty-four. Counting the actual weightTwoBasis therefore proves finrank 98304 for the original weight-two eigenspace. Neither an alternate existential ground representation nor an assumed Jacobi law is introduced.")),
            Paragraph(Text("This is only the native twisted weight-two space. It is not a claim about an untwisted dimension, the coefficient 196884, a realized moonshine module, the Monster group, fusion, anomaly cancellation or gluing.")))));
}
