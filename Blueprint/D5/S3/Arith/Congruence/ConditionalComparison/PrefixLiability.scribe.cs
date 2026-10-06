using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence.ConditionalComparison;

internal sealed class PrefixLiabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting every sufficiently deep progression in one prime-power parent exposes exactly the private region of its pure-power child, extended along the remaining prime-power coordinate.",
        H("Complete Prefix Liability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-prefix-liability"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ConditionalComparison/PrefixLiability.prefix_liability"),
                H("The complete deletion hole retains every cofactor coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite family of progressions A_i = [r_i] modulo d_i cover all natural numbers. "
                        + "Let q be prime, let R be coprime to q, and suppose every d_i "
                        + "divides q^G R. For natural k and G, fix an index j with d_j = q^(k+1). "
                        + "Delete precisely the indices J for which q^(k+1) divides d_i and "
                        + "r_i agrees with r_j modulo q^k. Suppose every deleted progression other than A_j "
                        + "has a point outside A_j.")),
                    Paragraph(Text(
                        "Write E for all points missed by the retained progressions, and P_j for those "
                        + "points of A_j missed by every other original progression. For every natural x, "
                        + "x belongs to E if and only if x agrees with r_j modulo q^k and there exists "
                        + "y in P_j agreeing with x modulo R.")),
                    Paragraph(Text(
                        "Whole coverage places the deletion hole inside the chosen parent. A retained "
                        + "progression with lower q-height tests only the parent prefix and the R coordinate; "
                        + "a retained progression with higher q-height misses the entire parent. These "
                        + "memberships therefore remain unchanged when only the remaining q digits vary.")),
                    Paragraph(Text(
                        "Another deleted progression meeting the pure child would be contained in it, "
                        + "contrary to the stated noncontainment. Thus the deletion hole restricted to that "
                        + "child is exactly P_j. The Chinese remainder theorem supplies a point of that "
                        + "child with any prescribed R coordinate, giving both directions of the identity.")),
                    Paragraph(Text(
                        "The identity retains the full cofactor R and the literal parent residue. It "
                        + "does not identify private regions with arbitrary joint deletion holes. Oddness, "
                        + "distinct numerical moduli and nonemptiness of P_j are not required."))),
                DescribeRole.Theorem))));
}
