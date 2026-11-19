using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetCanonicalIntertwinerDocument : IScribeDocumentDefinition
{
    private static DocumentBlock D(string selector, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticecosetcanonicalintertwiner-" + selector.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetCanonicalIntertwiner." + selector),
        H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetCanonicalIntertwiner", H("Complete rational Hahn lattice-coset fields"), Blocks(
            D("shift", "The rational offset is the original inverse-Gram pairing of external labels through the integral cross block B. External rank is arbitrary, including zero; the ambient block has lower-right block zero and need not be positive or nonsingular.", DescribeRole.Definition),
            D("intertwiner", "The full native compressedField is reindexed by the order embedding k maps to shift plus k in rational Hahn exponents. It is complex linear in both complete original carrier arguments. No prescribed ground coefficient, charge law or exponent-support predicate is added to an intertwiner law.", DescribeRole.Definition),
            D("field_coeff", "For every D, finite external rank, integral B, labels a,b, complete original states u,v and integer k, the reindexed field coefficient at shift+k is exactly the original compressed coefficient at k. It identifies the reindexed modes and the ground coefficient.", DescribeRole.Theorem),
            D("field_coeff_off", "At every rational exponent outside the full image shift+Z the field coefficient is zero for all u,v. It gives source linearity and the off-coset Jacobi and derivative laws.", DescribeRole.Theorem),
            D("mode_integer", "At rational mode m-shift for every integer m, the canonical field is the actual native compressed mode m on every source and input. The raw exponent convention is minus mode minus one. It transfers integer Jacobi and translation identities to the rational exponent coset.", DescribeRole.Theorem),
            D("ground_coefficient", "At raw exponent shift, the canonical field on both original vacuum states has coefficient exactly vacuum, the old-charge-zero oscillator-constant vector. The original external ground pairing is zero and its cocycle sign is one. Taking its constant coordinate gives ground_scalar.", DescribeRole.Theorem),
            D("ground_scalar", "The old-charge-zero oscillator-constant coordinate of that actual raw-shift coefficient is exactly one. This is derived from the native field, not an assumption. It proves nonvanishing and the normalization of groundEvaluation in additive fusion.", DescribeRole.Theorem),
            D("intertwiner_ne_zero", "For every original lattice and every finite external rank, B and external a,b, the source-linear full Hahn intertwiner is nonzero. It makes scalarInclusion injective, giving scalarEquiv its right inverse.", DescribeRole.Theorem),
            Paragraph(Text("Classical conventions: Bakalov--Kac, math/0402315v1, section 4.1. Native residue and conformal sources retain Scott Carnahan and Kalle Kytölä attributions. No mathematical novelty, physical realization, categorical fusion completion or string completion is claimed. The original rank may be zero; all external-rank statements also include zero.")))));
}
