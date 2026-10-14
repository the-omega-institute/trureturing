using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.RelativePairing;

internal sealed class NativeTransverseCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native finite coefficients recover the original relative transverse energy-sector states.",
        H("Native Transverse Coordinates"),
        Blocks(
            Paragraph(Text("The source is the actual complex Finsupp on TransverseDownIndex at a fixed lattice charge and integer level. Its indices are native oscillator monomials with zero occupation on both distinguished frame axes and empty polarized ghost word. No finite occupation cutoff is imposed. The state map uses the original coordinateSub and down. Both frame inverse equations and, for energy support, both Gram inverse equations remain explicit.")),
            Describe.Lean(DescribeId.Create("native-transverse-coordinate-left-inverse"),
                DeclarationHandle.Create(Prefix + "coordinates_downState"),
                H("Coefficient recovery"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("coordinates restricts the actual nativeCoefficients linear map along the injective native index powers to (powers, empty). Applying it to downState recovers every finite complex coefficient family exactly. The restriction is a Finsupp comapDomain, so finite support is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-transverse-projector-diagonal"),
                DeclarationHandle.Create(Prefix + "projector_coordinates"),
                H("Actual projector in native coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("P_native is extended through the original charge-sector finite basis expansion. The native coefficient at an index survives precisely when its actual kappa occupation is zero. No replacement projector or supplied transverse-membership premise occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-transverse-coordinate-right-inverse"),
                DeclarationHandle.Create(Prefix + "downState_coordinates"),
                H("Reconstruction of every relative projector-fixed state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a state in originalEnergySector fixed by the actual P and killed by the original B(0), every nonzero native coefficient has zero occupation on the two axes. kappa_zero_iff restricts the polarized ghost word to the epsilon site; native_relative_support excludes that site. Thus the ghost word is genuinely empty. nativeT0_support_level places the oscillator monomial in the exact TransverseDownIndex. A support-surjective native index embedding and sum_comapDomain then reconstruct the original state, not merely an abstract isomorphic carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-transverse-energy-input-state"),
                DeclarationHandle.Create(Prefix + "energyInput_state"),
                H("Existing reduced inputs are the native state map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full-state value of energyTransverseDownCombination is exactly downState. This consumed interface identifies the existing finite HPL inputs with the actual coefficient representation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-transverse-tensor-state"),
                DeclarationHandle.Create(Prefix + "downState_tensor"),
                H("Literal oscillator tensor down"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual state is Finsupp.single at the chosen charge of transverseDownOscillator, tensor the original down ghost. These coordinate consequences do not assert positivity or any no-ghost or radical conclusion."))),
                DescribeRole.Theorem))));
}
