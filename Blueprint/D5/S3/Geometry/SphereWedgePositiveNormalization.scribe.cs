using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class SphereWedgePositiveNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/SphereWedgePositiveNormalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary pointed sphere wedges admit actual positive-bouquet and isolated-point normal forms.",
        H("Pointed sphere wedge normalization"),
        Blocks(
            Node("positive-index", "PositiveIndex", "Positive sphere indices",
                "For arbitrary J and dimensions n:J to Nat, PositiveIndex consists of j with 0<n(j). No connected-component assertion is built into this subtype.", DescribeRole.Definition),
            Node("zero-index", "ZeroIndex", "One isolated point per zero sphere",
                "ZeroIndex is the subtype n(j)=0, equipped with the discrete topology. Every such index is retained, regardless of the size of the family.", DescribeRole.Definition),
            Node("positive-wedge", "PositiveWedge", "The genuine positive quotient bouquet",
                "Use CompactWedgeFiniteFactor.FamilyWedge with the original positive sphere dimensions and EuclideanSphereJoin.coordinatePoint basepoints. Its extra Unit representative retains the common point when there are no positive factors.", DescribeRole.Definition),
            Node("normalization", "normalizationHomeomorph", "Actual continuous maps and both inverse identities",
                "For arbitrary supplied sphere points b(j), reflect in the orthogonal complement of the span of b(j)-coordinatePoint(n(j)). Public Mathlib Submodule.reflection_sub sends b(j) exactly to the coordinate point, even when these vectors coincide. The linear isometry restricts to the actual unit sphere. In dimension zero, EuclideanSpace.sphere_zero_eq and the scalar square equation give precisely the two coordinate poles. The resulting finite T1 sphere is discrete. On a positive factor, send the normalized sphere point to its positive-bouquet class; on a zero factor send the coordinate pole to the common basepoint and the opposite pole to its ZeroIndex point. The extra Unit representative also maps to the common basepoint. These maps descend through the actual quotient relation. The inverse includes positive factors after the inverse reflection, and sends each zero index to its opposite pole after the inverse reflection. Continuity follows factorwise from the coproduct and quotient universal properties; both identities are proved on raw representatives. No quotient/subspace topology identification, arbitrary unbased wedge equivalence, finiteness assumption, homology or noncontractibility is used. All-zero families retain the basepoint and one additional isolated point for every factor; the empty family retains one point. This elementary construction is RepoDerived, without a novelty or exact literature-attestation claim.", DescribeRole.Definition),
            Node("base", "normalization_base", "The basepoint remains in the positive bouquet",
                "The normalization sends the original common basepoint exactly to the left summand's common basepoint. This equality is consumed by the pointed dependent-coproduct endpoint.", DescribeRole.Theorem),
            Node("coproduct", "coproductNormalizationHomeomorph", "Pointed dependent outer coproduct normalization",
                "For arbitrary dependent outer and inner families, apply the one-wedge homeomorphism in each outer summand and distribute the dependent coproduct over the two summands. The result bundles an actual homeomorphism to the coproduct of positive bouquets plus the dependent coproduct of zero indices, together with its exact action on every original outer basepoint. Both distribution maps are continuous by the native coproduct universal properties. Empty positive selections retain one point for every original outer index, while an empty outer type stays empty. Finite selected original indices from CompactWedgeFiniteFactor therefore yield finite normal-form indices without asserting that the unselected original indices were finite. This endpoint supplies the normalization step of the Carnero Bravo Question 22 route; the full composition-closure question remains separate and unresolved here.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
