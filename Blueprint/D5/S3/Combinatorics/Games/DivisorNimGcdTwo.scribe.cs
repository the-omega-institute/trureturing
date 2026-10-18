using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class DivisorNimGcdTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/DivisorNimGcdTwo.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive fixed multiset with at least two occurrences and gcd two, "
            + "the comparison spacing is an eventual period of the full native SG sequence.",
        H("Full comparison spacing at gcd two"),
        Blocks(
            Paragraph(Text("The carrier, occurrence-selected moves, deletion convention and SG "
                + "values are those of the native Divisor Nim game. At n=0 the varying heap is "
                + "omitted. No bound is imposed on heap sizes, heap counts or multiplicities. "
                + "The comparison spacing W is the least common multiple of lcm(1,...,min A) "
                + "and the actual least positive eventual periods of every nonempty direct "
                + "fixed successor. Eventual-period existence is established for all positive "
                + "nonempty fixed boards in DivisorNimFixedBoard.")),
            Node("zero-residue", "The zero residue at arbitrary dyadic depth", "fixed_zero_residue",
                "Let A be positive with minimum dyadic depth k, and let n be positive. The "
                    + "actual value g(n adjoined to A) is zero exactly when n modulo two to "
                    + "the power k+1 is zero if the number of depth-k fixed heaps is even, "
                    + "and two to the power k otherwise. This follows from the native "
                    + "minimum-depth outcome criterion, including n below the fixed depth."),
            Node("zero-period-divisibility", "Every full period preserves the zero residue",
                "zero_residue_period_dvd",
                "Under the same positive-board and minimum-depth assumptions, every full "
                    + "eventual SG period T is divisible by two to the power k+1. A losing "
                    + "index can be chosen beyond the tail threshold; its translate by T "
                    + "must lie in the same unique zero residue."),
            Node("gcd-two-zero-pattern", "The omission-aware zero pattern", "gcd_two_zero_pattern",
                "For every positive fixed A of gcd two and every natural n, fixedSequence A n "
                    + "is zero exactly when n modulo four is two if countAt A 1 is odd, "
                    + "and zero if it is even. The statement includes n=0 with no extra heap."),
            Node("odd-fixed-options", "All actual fixed options at an odd varying heap",
                "gcd_two_odd_fixed_values",
                "For positive fixed A of gcd two and odd n, the full fixedMoveValues A n "
                    + "is exactly the singleton zero. Every legal removed amount divides "
                    + "the odd varying heap and is odd. The selected fixed heap is even, "
                    + "so its remainder is positive and odd. Together with the untouched "
                    + "varying heap this gives two minimum-depth heaps. Removing one from "
                    + "any fixed heap provides an actual option, proving nonemptiness."),
            Node("literal-gcd-two-recurrence", "The complete two-step recurrence",
                "gcd_two_recurrence",
                "For positive fixed A of gcd two and n at least two, fixedSequence A n is "
                    + "mex of the two actual lookbacks at n-1 and n-2 together with the full "
                    + "fixedMoveValues A n. Empty fixed successors remain included. In "
                    + "particular the boundary lookback at zero uses omission."),
            Node("odd-recurrence", "Odd values and their exact recurrence", "gcd_two_odd_recurrence",
                "At every odd n at least three, the full native recurrence is "
                    + "f(n)=mex{0,f(n-1),f(n-2)}. Its value lies between one and three."),
            Node("four-divides-spacing", "The minimum-two successor branch",
                "gcd_two_four_dvd_spacing",
                "For every positive fixed A with at least two occurrences and gcd two, "
                    + "four divides W. If the minimum is at least four, four divides "
                    + "lcm(1,...,min A). If the minimum is two, deleting one fixed two is "
                    + "an actual legal move and leaves a nonempty all-even board B. Its "
                    + "minimum depth k is at least one. The zero-residue theorem forces "
                    + "two to the power k+1, hence four, to divide its actual least period, "
                    + "which divides W."),
            Describe.Lean(DescribeId.Create("full-spacing"),
                DeclarationHandle.Create(Prefix + "gcd_two_spacing"),
                H("The full period and multiplier one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive multiset A with at least two occurrences "
                        + "and gcd two, W is an eventual period of the actual full SG sequence, "
                        + "the actual least positive eventual period Q divides W, and "
                        + "Q/gcd(Q,W)=1. The theorem assumes no parent period.")),
                    Paragraph(Text("Take late consecutive zero indices z+4t. Write a(t), b(t), "
                        + "c(t) for the next three actual SG values, and S(t) for the full "
                        + "fixed-option value set at z+4t+2. The exact recurrences are "
                        + "a(t+1)=mex{0,c(t)}, b(t)=mex({0,a(t)} union S(t)), and "
                        + "c(t)=mex{0,a(t),b(t)}. If c(t)=1 then a(t+1)=2, and c(t+1) "
                        + "is one when one belongs to S(t+1), otherwise three. If c(t) "
                        + "is different from one then a(t+1)=1, and c(t+1) is two when "
                        + "two belongs to S(t+1), otherwise three.")),
                    Paragraph(Text("These four cases prove that c cannot return to one after "
                        + "leaving it. Both alternatives are retained: c remains one and a "
                        + "is eventually two, or c leaves one permanently and a is eventually "
                        + "one. In either case b and c are determined by a and the full set S. "
                        + "The actual fixed-option sets eventually repeat after W, and four "
                        + "divides W. All four phases therefore repeat after W. Division with "
                        + "remainder by four reconstructs every sufficiently late native SG "
                        + "value. The least-period divisibility theorem then gives Q dividing "
                        + "W and the stated quotient.")),
                    Paragraph(Text("This proves the complete gcd-two family. General fixed-gcd "
                        + "multipliers, unbounded mixed two/four least-period formulas, "
                        + "arbitrarily many heaps of four, and universal bound optimality "
                        + "remain separate questions. No finite numerical table is used "
                        + "as an infinite-family proof."))), DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
