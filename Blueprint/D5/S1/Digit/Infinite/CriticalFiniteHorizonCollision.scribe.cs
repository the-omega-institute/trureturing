using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class CriticalFiniteHorizonCollisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict critical collisions at every finite horizon.",
        H("Strict critical collisions at every finite horizon"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("criticalfinitehorizoncollision-finite-cylinder-sides"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/CriticalFiniteHorizonCollision.finite_cylinder_sides"),
                H("Finite sources on both sides of an interior cylinder coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let t be the reciprocal golden ratio, g = t cubed, and yStar = (t - 4) / 5. "
                        + "Every finite legal window prefix, with either incoming guard, has a nondegenerate "
                        + "closed scalar interval. Both endpoints belong to the image of the integral golden "
                        + "ring under its real embedding, equivalently to the ring of numbers m + n t with "
                        + "integer m and n. This includes the empty prefix.")),
                    Paragraph(Text(
                        "The coordinate yStar lies strictly between -1 and t and is outside that ring. "
                        + "Consequently it is strictly inside every finite cylinder of an actual guard-one "
                        + "address encoding it. In each such cylinder and for every positive epsilon there "
                        + "are two legal addresses that eventually become zero: one has coordinate strictly "
                        + "between yStar - epsilon and yStar, and the other strictly between yStar and "
                        + "yStar + epsilon. Both retain the same prescribed prefix and incoming guard.")),
                    Paragraph(Text(
                        "A finite prefix changes the terminal scalar by an affine map whose nonzero slope "
                        + "is a power of -g. The constant term is the coordinate of the same prefix followed "
                        + "by zeros and hence belongs to the integral golden ring. Realizing nearby interior "
                        + "scalars and then retaining sufficiently many further windows before appending "
                        + "zeros gives the required finite sources on the two sides."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("criticalfinitehorizoncollision-result"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/CriticalFiniteHorizonCollision.result"),
                H("A strict collision for every fixed finite color record"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set lambda = t squared / 10 and use the six critical cells with cuts "
                        + "-t squared - lambda, g - 3 lambda, t - 5 lambda, 2t - 7 lambda, and "
                        + "2t + lambda. Let Q assign every point of the support [-1, 1+t] to a cell "
                        + "whose closure contains that point; a cut may be assigned to either adjacent cell. "
                        + "For every natural h, there are two actual legal addresses that eventually become "
                        + "zero and start respectively with the three and null labels. There are errors "
                        + "at each of the h+1 sample times whose absolute values are strictly below lambda "
                        + "and whose clipped color records under Q coincide coordinate by coordinate.")),
                    Paragraph(Text(
                        "Choose two finite guard-one tails on opposite sides of yStar in a sufficiently "
                        + "long common cylinder. Prepending the three and null labels puts their current "
                        + "coordinates just inside the two extreme sides of the first critical gap. "
                        + "Strictly smaller errors move both targets into the interior of the same cell, "
                        + "so their current colors agree independently of endpoint assignments.")),
                    Paragraph(Text(
                        "At every remaining time through h, the tails retain a long common prefix. "
                        + "The scalar difference is bounded by the support diameter times the corresponding "
                        + "power of g and can be made strictly below twice lambda. Move both coordinates "
                        + "to their common midpoint. Each error is strictly below lambda, the midpoint lies "
                        + "in the support, and the future colors agree. Clipping therefore fixes all the "
                        + "chosen targets. For h = 0 only the current targets are needed.")),
                    Paragraph(Text(
                        "The two complete finite sources determine all their own sample coordinates. "
                        + "The pair may depend on h; the assertion does not supply one pair with a collision "
                        + "over the entire infinite future."))),
                DescribeRole.Theorem))));
}
