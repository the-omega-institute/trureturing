using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class IntegerStrongOrderingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Sequenceability/IntegerStrongOrdering.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/kravitz2024rearranging");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer orderings with no proper nonempty zero-sum interval.",
        H("Strong integer orderings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-strong-ordering"),
                DeclarationHandle.Create(Prefix + "exists_integer_strong_ordering"),
                H("Every finite nonzero integer set has a strong ordering"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every finite set A of integers excluding zero, there is "
                        + "a list w permuting A.toList. For every pair of natural indices i < j "
                        + "with j at most the length of w, the sum of take (j-i) (drop i w) "
                        + "is nonzero whenever i is nonzero or j is not the full length. "
                        + "Only the complete word is exempt. Empty sets, singleton sets, "
                        + "either empty sign block and equal positive and negative totals "
                        + "are included.")),
                    Paragraph(Text("The private construction simultaneously orders positive "
                        + "sets P and N so equal bounded prefix sums occur only at the "
                        + "empty pair or the full pair. Strong induction on card(P)+card(N) "
                        + "allows either side to become the larger-total side at each call. "
                        + "For a side with at least two elements, cancellation shows that "
                        + "at most one deletion leaves the opposite total. Delete another "
                        + "element, recurse and append it. Its deletion inequality removes "
                        + "the old full-pair collision, and total dominance excludes a new "
                        + "collision with a proper prefix.")),
                    Paragraph(Text("The final word is reverse(p) followed by map neg n. "
                        + "Positive-prefix strictness handles intervals within either sign "
                        + "block. A cross-block collision is exactly an equality between "
                        + "the constructed positive prefixes and forces the initial and "
                        + "final endpoints. Prefix splitting gives the full interval claim. "
                        + "Distinctness is within each positive set; cross-sign shared "
                        + "magnitudes are allowed.")),
                    Paragraph(Text("This formalizes Kravitz, Theorem 1.3 and Remark (1), "
                        + "arXiv:2407.01835v2, pages 2-3. Kravitz credits a similar route "
                        + "to Sawin's 2015 MathOverflow contribution. The result is known "
                        + "mathematics. The retained construction supplies an unbounded "
                        + "simultaneous recursion absent among the inspected formal "
                        + "suppliers. It does not solve the arbitrary abelian-group or "
                        + "integral-primitive target, and implements no ordered-kernel "
                        + "extension."))),
                DescribeRole.Theorem))));
}
