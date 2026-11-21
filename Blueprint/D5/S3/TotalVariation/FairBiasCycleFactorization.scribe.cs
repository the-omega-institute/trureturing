using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasCycleFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed fair-bias cycle coefficients are an oriented circuit-boundary product.",
        H("Circuit products for signed fair-bias cycles"),
        Blocks(Describe.Lean(
            DescribeId.Create("signed-cycle-factorization"),
            DeclarationHandle.Create(
                "D5/S3/TotalVariation/FairBiasCycleFactorization.signed_cycle_factorization"),
            H("Signed fair-bias cycles and their support sizes"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a finite binary column family and a total order on its signed labels. "
                    + "The augmented top facets are the nonempty facets when they exist and "
                    + "the empty face in rank zero. An augmented top facet has full restriction "
                    + "exactly when every vertex has a smaller exchange in the signed matroid.")),
                Paragraph(Text(
                    "At every full-restriction augmented top facet B there is a unique integral "
                    + "cycle with top-facet support, zero signed boundary matrix product, and "
                    + "Kronecker-delta coordinates at B on the full-restriction top facets. "
                    + "In rank zero this is the chain concentrated at the empty face with "
                    + "coefficient one.")),
                Paragraph(Text(
                    "Let e be the least nonloop of the signed matroid and C its fundamental "
                    + "circuit at B. The difference D of B with C is internally passive after "
                    + "contracting C. At each augmented signed face, the normalized cycle "
                    + "coefficient is the signed join of the circuit simplex boundary with the "
                    + "normalized contracted cycle at D, oriented to have coefficient one at B.")),
                Paragraph(Text(
                    "In the signed boundary matrix the entry for a deletion uses the number "
                    + "of vertices preceding the deleted one. This equals the insertion count "
                    + "at the resulting ridge, giving the same signs in ambient face coordinates. "
                    + "A signed face lies in the support precisely when it omits one circuit "
                    + "vertex and its outside part lies in the contracted support. The support "
                    + "has circuit size times the number of contracted support faces."))),
            DescribeRole.Theorem))));
}
