using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SumInConcatenationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SumInConcatenation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/hasler2023a359482");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The greedy decimal sequence A359482 omits every single-digit successor and therefore omits 2.",
        H("A359482 is not a permutation"),
        Blocks(
            Paragraph(Text(
                "All variables are natural numbers. D(x) is the decimal digit list with the most "
                + "significant digit first, no leading zeros, and D(0)=[0]. Legal(x,y) means that "
                + "D(x+y) is a contiguous sublist of D(x) followed by D(y). For example, 11 occurs "
                + "in 110, 109 in 1099, and 988 in 99889.")),
            Paragraph(Text(
                "The initial state is (1,{1}). Given the current term x and finite used set U, "
                + "next(x,U) is the natural infimum of positive y outside U satisfying Legal(x,y). "
                + "The next state is (next(x,U), U union {next(x,U)}). The function seq(n) reads "
                + "the current term after n-1 steps; seq(1)=1, and seq(0)=1 by convention.")),
            Node("no_small_successor", "No positive single-digit successor", NoSmall(),
                "The sum has at least as many digits as x. Reverse the occurrence and split at "
                + "its first position: an occurrence wholly in the old digits forces x+d=x. "
                + "Otherwise it is a prefix of d followed by those digits, with at most one "
                + "digit left over. No leftover forces x+d=d+10x. A leftover a gives old digits "
                + "r followed by a and sum digits d followed by r. Evaluation forces "
                + "a times 10^length(r)=9 times value(r). Modulo nine gives a=0 or a=9. "
                + "The first forces x=0; the second forces value(r)=10^length(r), contradicting "
                + "the strict digit-value bound. The empty list r is included."),
            Node("sequence_greedy", "The original least-unused rule", Greedy(),
                "Here candidates(k) consists exactly of positive y such that y differs from "
                + "seq(i+1) for every 0<=i<=k and Legal(seq(k+1),y) holds. Induction identifies "
                + "the stored used set with the image of the preceding indices. Thus this "
                + "equality states the original lexicographic greedy rule."),
            Node("sequence_pos", "Positive terms at every index", Positive(),
                "Put P=10^length(D(x)), R(0)=x, R(k+1)=x+P R(k). The digits of R(k) repeat "
                + "D(x), and P R(k) is a legal successor: the sum occurs before the trailing "
                + "zero block in the concatenation. These successors exceed k, so one lies "
                + "outside every finite used set. The defining infimum therefore belongs to "
                + "the positive candidate set. Induction proves positivity of all terms."),
            Node("sequence_legal", "Adjacent terms satisfy the substring rule", Adjacent(),
                "The same nonempty candidate set ensures that each chosen minimum satisfies "
                + "the decimal substring condition."),
            Node("sequence_tail_ge_ten", "Every term after the first is at least ten", Tail(),
                "Positivity and the adjacent-pair rule allow the no-single-digit theorem "
                + "to be applied at every index from two onwards."),
            Node("not_positive_permutation", "The positive integer two is missing", NotOnto(),
                "The first term is 1. Every later term is at least 10. Hence 2 has no positive "
                + "index, so the sequence is not surjective onto the positive integers and "
                + "cannot be a permutation. This answers the permutation question in OEIS "
                + "A359482; it does not address the stronger multiples-of-ten conjecture.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a359482-positive-permutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a359482-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula S(Formula n) => Call("seq", n);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Bound(string name) => Seq(
        Forall, Sp, V(name), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp);
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula NoSmall() => Disp(Seq(Bound("x"), Bound("d"),
        D(0), Sp, Lt, Sp, V("x"), Sp, Implies, Sp,
        Paren(Seq(D(0), Sp, Lt, Sp, V("d"), Sp, Land, Sp, V("d"), Sp, Lt, Sp, D(1, 0))),
        Sp, Implies, Sp, Neg, Call("Legal", V("x"), V("d"))));
    private static Formula Greedy() => Disp(Seq(Bound("k"),
        S(Add(V("k"), D(2))), Sp, Eq, Sp, Call("sInf", Call("candidates", V("k")))));
    private static Formula Positive() => Disp(Seq(Bound("n"), D(0), Sp, Lt, Sp, S(V("n"))));
    private static Formula Adjacent() => Disp(Seq(Bound("n"), D(1), Sp, Le, Sp, V("n"),
        Sp, Implies, Sp, Call("Legal", S(V("n")), S(Add(V("n"), D(1))))));
    private static Formula Tail() => Disp(Seq(Bound("n"), D(2), Sp, Le, Sp, V("n"),
        Sp, Implies, Sp, D(1, 0), Sp, Le, Sp, S(V("n"))));
    private static Formula NotOnto() => Disp(Seq(Neg, Paren(Seq(Bound("m"),
        D(0), Sp, Lt, Sp, V("m"), Sp, Implies, Sp,
        Exists, Sp, V("n"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
        D(1), Sp, Le, Sp, V("n"), Sp, Land, Sp, S(V("n")), Sp, Eq, Sp, V("m")))));
}
