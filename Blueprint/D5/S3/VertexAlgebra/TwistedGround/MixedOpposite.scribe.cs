using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class MixedOppositeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Source-linear opposite field on the actual fixed restricted dual",
        H("Source-linear opposite field on the actual fixed restricted dual"),
        Blocks(
            Paragraph(Text("The source is the original theta-fixed lattice carrier. The target is the same full fixed restricted dual used by MixedIntertwiner. For a source of weight d, the opposite original-space mode maps grade e to e+m-d+1. Its pullback on the restricted dual maps grade E to E+d-m-1. These are the original typed maps from MixedIntertwiner.")),
            Paragraph(Text("The source L1 expansion is finite at the existing actual oscillator support bound. Rewriting the finite expansion as a finitely supported sum proves additivity and scalar linearity despite the source-dependent cutoff. Direct-sum extension then makes the opposite homogeneous mode a linear endomorphism of the entire restricted dual.")),
            Paragraph(Text("For an arbitrary fixed source, each original energy projection is averaged with its theta image. The conformal state is theta-fixed, so the existing actual L0 grade criterion proves that this average retains its energy and belongs to the fixed carrier. Only the finite original stateEnergies can contribute. The resulting source-linear action agrees exactly with the typed opposite action on every homogeneous fixed source.")),
            Paragraph(Text("Positive original source energy kills negative fixed grades. If m exceeds the sum of the nonnegative upper bounds for the source energy support and the restricted-dual input support, each opposite term has negative output grade and vanishes. This supplies an actual opposite formal field with standard mode m. No invariant-form identification of the output with the source is used.")),
            Paragraph(Text("This construction is a repository Lean derivation using the existing original source, Sugawara, involution and finite L1 suppliers. MixedJacobiFinite.mixed_jacobi proves the full signed normalized mixed Jacobi identity with this actual opposite action under positive real Gram, unit determinant and rank twenty-four, using support-controlled transformation of the three-supported original twisted law and both right-hand branches. MixedJacobi.actual_leech_vacuum_channel supplies a nonzero I_3 channel on the actual Golay Leech data. Full source BPZ/Riesz identification, skew exchange, three-twisted crossing, full fusion and anomaly structure, complete VOA/CFT, string theory and AdS/CFT remain separate obligations.")),
            Describe.Lean(DescribeId.Create("opposite-homogeneous-extension"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedOpposite.oppositeAction_homogeneous"),
                H("Exact homogeneous compatibility of the full opposite action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual homogeneous fixed source, the source-linear action on the whole fixed restricted dual is exactly the direct-sum extension of the original typed opposite dual maps. The proof identifies every actual energy projection, including all excluded source weights."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("opposite-field-truncation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedOpposite.oppositeAction_truncation"),
                H("All-source and all-vector opposite-mode truncation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cutoff is the sum of the finite source-energy upper bound and the finite restricted-dual input-energy upper bound. The original-space and dual-space degree directions are retained, and the positive-Gram hypothesis is used to prove that every negative output grade is zero."))),
                DescribeRole.Theorem))));
}
