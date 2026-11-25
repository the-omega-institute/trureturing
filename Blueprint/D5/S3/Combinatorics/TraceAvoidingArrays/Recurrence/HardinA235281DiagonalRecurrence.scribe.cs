using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235281DiagonalRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Result = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence.result";
    private const string Note = "D5/L/Automata/hardin2014a235281";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The seven-lag recurrence for Hardin's square arrays.",
        H("Hardin's constant-stress square arrays"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Result),
                H("The seven-lag diagonal recurrence"),
                StatementSource.FromAuthor(Disp(RecurrenceStatement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("OEIS A235281 counts literal square fillings by 0 through 3 whose contiguous "
                        + "two-by-two blocks have absolute diagonal difference four. Its term at index m is the "
                        + "rectangular count T(m,m) of A235289, for a square of side m+1. The offset is one, so "
                        + "the displayed recurrence first computes term eight. The index arithmetic is natural "
                        + "and the signed count identity is over the integers.")),
                    Paragraph(Text("The rectangular profile sum counts each uniform block-sum-two filling twice "
                        + "to account for the two classes under complementation. Within the sum, a row with a "
                        + "prescribed profile is determined by any one cell. At an edge with sum s there are at "
                        + "most s+1 choices for its first cell. Thus the multiplicities of a profile and its "
                        + "complement add to at most three if the profile takes two different values. When both "
                        + "multiplicities are positive they are (1,1), (1,2) or (2,1). The three constant "
                        + "profiles have multiplicities 1, 2 and 3, obtained by alternating two entries with "
                        + "the prescribed sum.")),
                    Paragraph(Text("Write n+2 for the number of rows and k+2 for the number of columns. Let "
                        + "w(a,d,h) be the product of h alternating factors a,d,a,d,… beginning with a. Set "
                        + "U(n) = 2^(n+2) + w(1,3,n+2) + w(3,1,n+2) and "
                        + "V(n) = w(1,2,n+2) + w(2,1,n+2). The constant profiles contribute U(n). "
                        + "Write C(k) for the number of nonconstant profiles with pair (1,1) and D(k) for "
                        + "those with pair (1,2). Complementation pairs the (1,2) and (2,1) profiles, giving "
                        + "T(n+1,k+1) = 2(U(n) + C(k) + D(k)V(n)).")),
                    Paragraph(Text("Width two has only constant profiles. Transposing the width-two arrays "
                        + "and using V(0) = 4 eliminates C(k). Transposing against width three, where V(1) = 6, "
                        + "gives 2D(k) = D(1)(V(k) − 4). On the diagonal these identities give "
                        + "T(n+1,n+1) = 4U(n) − 2U(0) + D(1)(V(n) − 4)^2.")),
                    Paragraph(Text("Under a two-index shift the power of two in U is multiplied by four, "
                        + "the other part of U by three, V by two, and V squared by four. After expanding the "
                        + "square, the constant contribution is killed by E−1, where E shifts the index "
                        + "by one. The full diagonal is therefore annihilated by "
                        + "(E−1)(E^2−2)(E^2−3)(E^2−4). Expanding this polynomial gives the displayed "
                        + "coefficients."))),
                DescribeRole.Theorem))));

    private static Formula RecurrenceStatement()
    {
        var m = F.Id("m");
        Formula At(Formula index) => Call("T", index, index);
        Formula Lag(byte offset) => At(Add(m, D(offset)));

        var right = Add(Lag(6), Multiply(D(9), Lag(5)));
        right = Subtract(right, Multiply(D(9), Lag(4)));
        right = Subtract(right, Multiply(D(2, 6), Lag(3)));
        right = Add(right, Multiply(D(2, 6), Lag(2)));
        right = Add(right, Multiply(D(2, 4), Lag(1)));
        right = Subtract(right, Multiply(D(2, 4), At(m)));

        var lowerBound = Seq(D(1), Sp, Le, Sp, m);
        return Seq(Forall, Sp, m, Colon, Sp, F.Id("Nat"), Comma, Sp,
            Parenthesized(Seq(Parenthesized(lowerBound), Sp, Implies, Sp,
                Parenthesized(Equal(Lag(7), right)))));
    }

    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
}
