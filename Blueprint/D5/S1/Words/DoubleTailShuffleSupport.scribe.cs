using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class DoubleTailShuffleSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/DoubleTailShuffleSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/layman2011a193020");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangular set of three unary gaps gives the exact distinct support of a double-tail self-shuffle.",
        H("Double-Tail Self-Shuffle Support"), Blocks(
            Paragraph(Text("All scalar variables are natural numbers. A word is a finite list of Boolean digits, "
                + "with true representing one and false representing zero. The ordinaryShuffles operation "
                + "completely consumes both operands in their internal order; converting its list of outputs "
                + "to a finite set removes schedule multiplicities. Subtraction and division below are "
                + "natural-number operations, with subtraction truncated at zero.")),
            Node("root", "Unary prefix and two terminal zeros", DescribeRole.Definition,
                All("m", NaturalType(), Equal(Call("root", F.Id("m")),
                    Qualified("List", "append", Qualified("List", "replicate", F.Id("m"), F.Id("true")),
                        Call("list", F.Id("false"), F.Id("false"))))),
                "The operand has m initial ones followed by exactly two zeros. Empty unary prefixes are allowed."),
            Node("self_shuffle_card", "Exact triangular cardinality", DescribeRole.Theorem,
                All("m", NaturalType(), Equal(
                    Call("card", Call("toFinset", Call("ordinaryShuffles", Call("root", F.Id("m")), Call("root", F.Id("m"))))),
                    Divide(Multiply(Parenthesized(Add(F.Id("m"), Num(2))), Parenthesized(Add(F.Id("m"), Num(1)))), Num(2)))),
                "Every output is a ones, zero, b ones, zero, c ones, zero, zero, where a+b+c=2m and a is at least m. "
                + "To see necessity, first shuffle a single zero against a unary prefix with two terminal zeros, "
                + "then two zeros against that word, and finally two unary prefixes by induction on their total length. "
                + "In each recursive branch the next digit comes from one operand, and all terminal zeros remain accounted for. "
                + "Conversely put i=b+c and j=b. For every pair 0<=j<=i<=m, read all m ones from the first copy, "
                + "m-i ones from the second, the first zero from the first copy, j ones from the second, "
                + "the second zero from the first copy, and finally the remaining i-j ones and two zeros from the second. "
                + "This produces precisely the three runs of lengths m+(m-i), j and i-j. The unary-gap uniqueness theorem "
                + "recovers i and j from the output word. Thus the support is an injective image of the triangular "
                + "parameter set, whose cardinality is the sum of i+1 for i from zero through m. This is an equality "
                + "of distinct-word cardinalities for every natural m, including zero."),
            Node("binary_root_original", "Ordinary numeral of a power minus four", DescribeRole.Theorem,
                All("k", NaturalType(), Seq(AtMost(Num(3), F.Id("k")), Implies, Sp,
                    Equal(Call("binaryWord", Subtract(Power(Num(2), F.Id("k")), Num(4))),
                        Call("root", Subtract(F.Id("k"), Num(2)))))),
                "For k at least three, the positive natural number 2^k-4 equals four times the quantity (2^(k-2)-1). "
                + "The latter factor has k-2 binary ones; multiplication by four appends two zeros. "
                + "The existing binaryWord definition reverses the least-significant-first base-two digits and "
                + "maps digit one to true. This is the ordinary numeral without leading zeros."),
            Node("result", "The full eventual minus-four identity", DescribeRole.Theorem,
                Seq(Exists, Sp, Natural("K"), Comma, Sp,
                    Parenthesized(Seq(AtMost(Num(3), F.Id("K")), Land, Sp,
                        All("k", NaturalType(), Seq(AtMost(F.Id("K"), F.Id("k")), Implies, Sp,
                            Equal(Call("distinctSelfShuffleCount", Subtract(Power(Num(2), F.Id("k")), Num(4))),
                                Divide(Multiply(F.Id("k"), Parenthesized(Subtract(F.Id("k"), Num(1)))), Num(2)))))))),
                "The published sequence counts distinct complete self-shuffle output words of an ordinary positive binary numeral. "
                + "Choose K=3. For every k at least K, the numeral identity identifies the operand with root(k-2), "
                + "and the exact support cardinality gives k*(k-1)/2. The existential threshold and every subsequent "
                + "index are retained. The definition of the sequence comes from OEIS A193020; the proof of this "
                + "minus-four assertion is the support argument given here.", AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a193020-minus-four-eventual-identity"),
                    ResolutionKind.Proved)))));

    private static Formula NaturalType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Natural(string name) => Parenthesized(Seq(F.Id(name), Colon, Sp, NaturalType()));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Divide(Formula a, Formula b) => Qualified("Nat", "div", a, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static DocumentBlock.Describe Node(string declaration, string title, DescribeRole role,
        Formula statement, string prose, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("double-tail-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(statement)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);
}
