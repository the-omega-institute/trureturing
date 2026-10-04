using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class RecordTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four actual separable record distributions share a rising side through record three.",
        H("Actual Record Symmetries and Rising Distributions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-four-record-transports-and-rising"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/RecordTransport.actual_four_record_transports_and_rising"),
                H("All lengths, exact singleton corrections and all four rising laws"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("i", F.Id("lmin"), F.Id("n"), F.Id("k")), Eq,
                    Call("i", F.Id("rmax"), F.Id("n"), F.Id("k")),
                    Sp, Land, Sp,
                    Call("d", F.Id("lmax"), F.Id("n"), F.Id("k")), Plus,
                    Call("delta", F.Id("n"), F.Id("k")), Eq,
                    Call("i", F.Id("rmax"), F.Id("n"), F.Id("k")),
                    Sp, Land, Sp,
                    Call("d", F.Id("rmin"), F.Id("n"), F.Id("k")), Plus,
                    Call("delta", F.Id("n"), F.Id("k")), Eq,
                    Call("i", F.Id("rmax"), F.Id("n"), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the literal permutations of Fin n avoiding 2413 and 3142. "
                        + "The count i(t,n,k) restricts to positive length and no proper direct cut; "
                        + "d(t,n,k) restricts to a proper direct cut. A direct cut separates a "
                        + "nonempty prefix whose values are all smaller than those of the nonempty "
                        + "suffix. The empty permutation belongs to neither positive class. "
                        + "The singleton is irreducible, and the reducible singleton class is empty.")),
                    Paragraph(Text(
                        "A right maximum exceeds every later value; a left maximum exceeds "
                        + "every earlier value. A right minimum is below every later value; "
                        + "a left minimum is below every earlier value. These comparisons are "
                        + "strict, and the counts are unshifted. The displayed identities hold "
                        + "for all natural n and k. The correction delta(n,k) equals one exactly "
                        + "when n=k=1, and equals zero otherwise.")),
                    Paragraph(Text(
                        "Let a(t,n,k) denote any of the four counts i(rmax,n,k), i(lmin,n,k), "
                        + "d(lmax,n,k) and d(rmin,n,k). The same theorem gives the following "
                        + "boundary and rising laws for each of these four choices.")),
                    Paragraph(Math(Disp(Seq(
                        F.Id("n"), Gt, D(0), Sp, Rightarrow, Sp,
                        Call("a", F.Id("t"), F.Id("n"), D(0)), Eq, D(0))))),
                    Paragraph(Math(Disp(Seq(
                        F.Id("n"), Ge, D(2), Sp, Rightarrow, Sp,
                        Call("a", F.Id("t"), F.Id("n"), D(1)), Eq, D(0))))),
                    Paragraph(Math(Disp(Seq(
                        F.Id("n"), Ge, D(4), Sp, Land, Sp,
                        F.Id("k"), Lt, D(3), Sp, Rightarrow, Sp,
                        Call("a", F.Id("t"), F.Id("n"), F.Id("k")), Le,
                        Call("a", F.Id("t"), F.Id("n"), Seq(F.Id("k"), Plus, D(1))))))),
                    Paragraph(Text(
                        "Reverse the positions, complement every value v to n-1-v, or perform "
                        + "both operations. Reversal and complementation each interchange the "
                        + "two forbidden patterns. Reversing a pattern occurrence reverses both "
                        + "its position indices and its embedded positions, giving an increasing "
                        + "embedding again. Complementation reverses the value comparisons. "
                        + "Thus all three involutions act on the actual avoidance class.")),
                    Paragraph(Text(
                        "Complementation flips a cut's sign and preserves its position. "
                        + "Reversal flips its sign and sends its position c to n-c. Both "
                        + "together preserve the sign. For n>=2, the separable pointwise cut "
                        + "dichotomy identifies the class without a proper skew cut with the "
                        + "class with a proper direct cut. Reversal sends right maxima to "
                        + "left maxima, complementation sends them to right minima, and both "
                        + "send them to left minima. Bijections of the record-position sets "
                        + "restrict these involutions to exact record fibers. This proves the "
                        + "three displayed identities, with the separate singleton correction.")),
                    Paragraph(Text(
                        "Every nonempty permutation has its last position as a right maximum. "
                        + "The position of its largest value is also a right maximum. If there "
                        + "were only one, those positions would coincide. At length at least "
                        + "two, this produces a proper direct cut at n-1, contradicting "
                        + "irreducibility. Hence the irreducible right-maximum fibers at zero "
                        + "and one records vanish in the stated ranges. The exact transports "
                        + "give the same boundaries for the other three distributions.")),
                    Paragraph(Text(
                        "Nonnegative cardinalities give the comparisons from zero to one and "
                        + "from one to two. The actual right-maximum comparison from two to "
                        + "three holds for every n>=4, and the three exact transports give it "
                        + "for the other distributions. Thus the complete rising side holds "
                        + "for all four actual record distributions. The inequalities beyond "
                        + "record three and a global peak-three maximum are not conclusions "
                        + "of this theorem."))),
                DescribeRole.Theorem))));
}
