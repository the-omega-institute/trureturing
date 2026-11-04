using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.SumInConcatenation;

internal sealed class DecimalMultiplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SumInConcatenation/DecimalMultiples.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/hasler2026a359482proof");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the original greedy decimal sequence A359482, 10 occurs at index 2 and none of 20,30,...,90 occurs at any index.",
        H("Two-digit multiples of ten in A359482"),
        Blocks(
            Paragraph(Text(
                "All variables are natural numbers. The decimal digit list D, substring predicate Legal, "
                + "least positive unused legal successor next, finite used-set state, and sequence seq "
                + "are those of SumInConcatenation. Indexing begins at 1, with seq(0)=seq(1)=1. "
                + "The legality condition uses the sum in the decimal concatenation, in the original order.")),
            Paragraph(Text(
                "Hasler's independent full proof establishes the published conjecture. The earlier "
                + "Ma-Zhang Lean contribution proves the single-digit part and supplies the sequence "
                + "definitions used here. The three-position argument below retains the exceptional "
                + "predecessor x=m before applying the sequence's tail bound.")),
            Node("legal_multiple_ten_iff", "Exact legal predecessors of a two-digit multiple of ten", LegalTens(),
                "Reverse the decimal occurrence. The concatenation begins with 0,m and then the digits of x. "
                + "The sum has at least as many digits as x, so there are three possible starting positions. "
                + "Writing q for ten to the number of digits of the sum, the first position gives 99x=qR. "
                + "Coprimality of q with 99 and 0<x<q exclude it. The second gives 9(x-m)=qR, "
                + "with m<=x; coprimality with 9 and x-m<q force x=m. A position entirely inside x "
                + "forces the sum to equal x, impossible for m>0. Conversely x=m satisfies the substring "
                + "rule for all nine admissible digits. This is the successor-multiple passage in Proof by MFH."),
            Node("sequence_ne_multiple_ten", "The terms 20 through 90 are absent at every index", Excluded(),
                "Indices 0 and 1 have value 1. At every later index, legality forces the preceding term "
                + "to be m. The preceding term is either the initial 1 or is at least 10; neither lies "
                + "between 2 and 9. The exclusion therefore holds even at the conventional index 0."),
            Node("sequence_multiple_ten_classification", "Ten occurs second and is the only such multiple", Classification(),
                "The candidate 10 is positive, unused after the initial 1, and legal because 11 occurs "
                + "in 110. The greedy minimum is at most 10, and the established tail bound is at least "
                + "10, so seq(2)=10. For 1<=m<10, the exclusion of 20 through 90 forces any occurring "
                + "10m to have m=1. Conversely index 2 supplies the positive index for m=1. "
                + "These statements concern the original decimal sequence; no conclusion about hundreds "
                + "or other bases follows."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("a359482-tens-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula S(Formula n) => Call("seq", n);
    private static Formula Times(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Bound(string name) => Seq(
        Forall, Sp, V(name), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp);
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula Range(Formula low) => Paren(Seq(low, Sp, Le, Sp, V("m"), Sp,
        Land, Sp, V("m"), Sp, Lt, Sp, D(1, 0)));
    private static Formula LegalTens() => Disp(Seq(Bound("x"), Bound("m"),
        D(0), Sp, Lt, Sp, V("x"), Sp, Implies, Sp, Range(D(1)), Sp, Implies, Sp,
        Paren(Seq(Call("Legal", V("x"), Times(D(1, 0), V("m"))), Sp, Iff, Sp, V("x"), Sp, Eq, Sp, V("m")))));
    private static Formula Excluded() => Disp(Seq(Bound("n"), Bound("m"), Range(D(2)), Sp,
        Implies, Sp, S(V("n")), Sp, Neq, Sp, Times(D(1, 0), V("m"))));
    private static Formula Classification() => Disp(Seq(S(D(2)), Sp, Eq, Sp, D(1, 0), Sp,
        Land, Sp, Paren(Seq(Bound("m"), Range(D(1)), Sp, Implies, Sp,
            Paren(Seq(Paren(Seq(Exists, Sp, V("n"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
                D(1), Sp, Le, Sp, V("n"), Sp, Land, Sp, S(V("n")), Sp, Eq, Sp,
                Times(D(1, 0), V("m")))), Sp, Iff, Sp, V("m"), Sp, Eq, Sp, D(1)))))));
}
