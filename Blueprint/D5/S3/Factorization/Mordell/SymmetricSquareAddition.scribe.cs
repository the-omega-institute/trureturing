using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class SymmetricSquareAdditionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous addition and subtraction.",
        H("Homogeneous addition and subtraction"),
        Blocks(
            Paragraph(Text("For every field F (the Lean interface uses [DecidableEq F], available classically), affine Weierstrass curve W, and nonsingular points P and Q, there is a nonzero scalar t such that t times sym2x(P + Q, P - Q) equals the homogeneous addition-and-subtraction map of W evaluated at sym2x(P, Q). Infinity, inverses and doubling are included in every characteristic.")),
            Paragraph(Text("The result is WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x, provided directly by the public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap. This module preserves the import interface and the simp attributes for negating either point. The theorem is owned by Mathlib.")),
            Paragraph(Text("The proof treats finite distinct points, inverses, infinity and doubling. Nonsingularity excludes simultaneous vanishing of the duplication numerator and denominator; the remaining coordinate identities follow from the curve and addition equations. Source: Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean, theorem sym2x_add_sub_eq_addSubMap_sym2x; mathematical source: "), Ref("D5/L/ArithUnits/tauceti2026canonicalheight")))));
}
