using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class EndpointShuffleSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/EndpointShuffleSupport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/layman2011a193020");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The endpoint-gap rectangle is exactly the distinct ordinary self-shuffle support.",
        H("Exact Endpoint-Word Shuffle Support"),
        Blocks(
            Paragraph(Text("Represent zero by false and one by true. Ordinary shuffles may take "
                + "the next symbol from either source, preserving each source's internal order. "
                + "The list ordinaryShuffles retains schedule multiplicities; conversion to a "
                + "finite set discards them. All cardinalities below count output words. All scalar indices are natural numbers.")),
            Node("endpointWord", "Two endpoint ones", DescribeRole.Definition,
                Equal(Call("endpointWord", F.Id("m")),
                    Call("List.append",
                        Call("List.append", Call("List.singleton", F.Id("true")),
                            Call("List.replicate", F.Id("m"), F.Id("false"))),
                        Call("List.singleton", F.Id("true")))),
                "The word consists of an initial one, m zeros and a final one. The value m=0 is allowed."),
            Node("endpointOutput", "Words parametrized by their outer gaps", DescribeRole.Definition,
                Equal(Call("endpointOutput", F.Id("m"), F.Id("a"), F.Id("c")),
                    Call("gap", F.Id("false"), Call("list", Num(1), Num(1), Num(1), Num(1)),
                        Call("list", Num(0), F.Id("a"),
                            Add(Parenthesized(Subtract(F.Id("m"), F.Id("a"))),
                                Parenthesized(Subtract(F.Id("m"), F.Id("c")))),
                            F.Id("c"), Num(0)))),
                "The five zero gaps around four ones are 0, a, (m-a)+(m-c), c and 0. "
                + "Natural subtraction is truncated: u-v means max(u-v,0), so this total definition "
                + "is unambiguous for arbitrary natural a and c. When a and c are at most m, "
                + "the total number of zeros is 2m; for example m=0,a=1,c=0 gives middle gap zero."),
            Node("endpointFamily", "The finite rectangle of output words", DescribeRole.Definition,
                Equal(Call("endpointFamily", F.Id("m")),
                    Call("Finset.image",
                        Lambda("p", PairType(F.Id("m")),
                            Call("endpointOutput", F.Id("m"),
                                Call("val", Call("fst", F.Id("p"))),
                                Call("val", Call("snd", F.Id("p"))))),
                        Parenthesized(Seq(Call("Finset.univ"), Colon, Sp,
                            Call("Finset", PairType(F.Id("m"))))))),
                "Take the image of Fin(m+1) times Fin(m+1) under the output map. "
                + "The map binds p in the full finite product and casts both projections with val. "
                + "The universal finite product includes every pair, including when m=0. "
                + "The image is a finite set of words, rather than a set of schedules."),
            Node("endpointOutput_mem", "Constructing every outer-gap pair", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, F.Id("a"), Comma, F.Id("c"), Comma, Sp,
                    AtMost(F.Id("a"), F.Id("m")), Land, Sp, AtMost(F.Id("c"), F.Id("m")), Implies, Sp,
                    Call("member", Call("endpointOutput", F.Id("m"), F.Id("a"), F.Id("c")),
                        Call("ordinaryShuffles", Call("endpointWord", F.Id("m")), Call("endpointWord", F.Id("m"))))),
                "Label the copies A and B. Read A for its initial one and a zeros, then B's "
                + "initial one, then the remaining m-a zeros from A and m-c zeros from B, "
                + "then A's last one, and finally B's c zeros and last one. Both source "
                + "orders are preserved, including when any of these zero blocks is empty."),
            Node("endpointFamily_card", "Distinct parameter pairs give distinct words", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, Sp,
                    Equal(Call("card", Call("endpointFamily", F.Id("m"))), Power(Add(F.Id("m"), Num(1)), Num(2)))),
                "The existing uniqueness theorem for unary-gap words recovers the outer gaps "
                + "from the resulting word. Thus the output map is injective and its finite "
                + "image has (m+1)^2 elements."),
            Node("endpoint_self_shuffle_card_lower", "A universal lower bound for distinct support", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, Sp,
                    AtMost(Power(Add(F.Id("m"), Num(1)), Num(2)),
                        Call("card", Call("toFinset", Call("ordinaryShuffles",
                            Call("endpointWord", F.Id("m")), Call("endpointWord", F.Id("m"))))))),
                "Every word in the parameter image belongs to the actual self-shuffle support. "
                + "Inclusion and the image cardinality give the displayed lower bound."),
            Node("endpoint_support_exhaustion", "Every output has two bounded outer gaps", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, F.Id("w"), Comma, Sp,
                    Call("member", F.Id("w"), Call("ordinaryShuffles", Call("endpointWord", F.Id("m")), Call("endpointWord", F.Id("m")))),
                    Implies, Sp, Exists, Sp, F.Id("a"), Comma, F.Id("c"), Comma, Sp,
                    AtMost(F.Id("a"), F.Id("m")), Land, Sp, AtMost(F.Id("c"), F.Id("m")), Land, Sp,
                    Equal(F.Id("w"), Call("endpointOutput", F.Id("m"), F.Id("a"), F.Id("c")))),
                "The first output symbol is an initial one of one source. Before the second "
                + "one there can only be zeros from that source, so their number a is at most m. "
                + "After the third one only one final one remains; its preceding c zeros belong "
                + "to that remaining source, so c is at most m. All four ones occur, no zeros "
                + "precede the first or follow the last, and the 2m zeros leave the middle gap "
                + "equal to (m-a)+(m-c). Recursively, shuffling two tails of r and s zeros "
                + "followed by one gives b zeros, one, c zeros, one, where b+c=r+s and "
                + "c is at most max(r,s). This supplies the bounds for every schedule, including "
                + "adjacent ones and all empty zero blocks."),
            Node("endpoint_support_eq", "Exact support equality", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, Sp,
                    Equal(Call("toFinset", Call("ordinaryShuffles", Call("endpointWord", F.Id("m")), Call("endpointWord", F.Id("m")))),
                        Call("endpointFamily", F.Id("m")))),
                "Universal exhaustion gives one inclusion; the explicit construction of each "
                + "bounded outer-gap pair gives the other. The equality concerns words with "
                + "duplicates discarded, regardless of how many schedules produce a word."),
            Node("endpoint_self_shuffle_card", "Exact cardinality for every zero-run length", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("m"), Comma, Sp,
                    Equal(Call("card", Call("toFinset", Call("ordinaryShuffles", Call("endpointWord", F.Id("m")), Call("endpointWord", F.Id("m"))))),
                        Power(Add(F.Id("m"), Num(1)), Num(2)))),
                "The support equals the injectively parametrized rectangle, whose cardinality "
                + "is (m+1)^2. This holds for every natural m, including m=0."),
            Node("binaryWord", "Ordinary binary numerals", DescribeRole.Definition,
                Equal(Call("binaryWord", F.Id("n")),
                    Call("List.map",
                        Lambda("d", NaturalType(),
                            Call("ite", Equal(F.Id("d"), Num(1)), F.Id("true"), F.Id("false"))),
                        Call("List.reverse", Call("Nat.digits", Num(2), F.Id("n"))))),
                "For positive n, use its ordinary finite base-two digits, reverse the "
                + "least-significant-first list to put the most significant digit first, and "
                + "map each natural digit d to true exactly when d=1, and to false otherwise. "
                + "The standard digits operation introduces no leading zeros. The definition "
                + "extends to n=0 by the empty list."),
            Node("distinctSelfShuffleCount", "Distinct output count", DescribeRole.Definition,
                Equal(Call("distinctSelfShuffleCount", F.Id("n")), Call("card", Call("toFinset", Call("ordinaryShuffles", Call("binaryWord", F.Id("n")), Call("binaryWord", F.Id("n")))))),
                "This is a(n): arbitrary order-preserving interleavings of two identical "
                + "ordinary binary numerals, counting each output word once.", Source),
            Node("binaryWord_pow_add_one", "Binary bridge at every positive exponent", DescribeRole.Theorem,
                Seq(Forall, Sp, F.Id("k"), Comma, Sp, AtMost(Num(1), F.Id("k")), Implies, Sp,
                    Equal(Call("binaryWord", Add(Power(Num(2), F.Id("k")), Num(1))), Call("endpointWord", Subtract(F.Id("k"), Num(1))))),
                "For every natural k at least one, the binary numeral of 2^k+1 is one, "
                + "k-1 zeros, one. The standard base-digit concatenation theorem gives this "
                + "identity directly; reversal preserves this particular word."),
            Node("result", "The eventual identity with threshold one", DescribeRole.Theorem,
                Seq(Exists, Sp, F.Id("K"), Comma, Sp, AtMost(Num(1), F.Id("K")), Land, Sp,
                    Forall, Sp, F.Id("k"), Comma, Sp, AtMost(F.Id("K"), F.Id("k")), Implies, Sp,
                    Equal(Call("distinctSelfShuffleCount", Add(Power(Num(2), F.Id("k")), Num(1))), Power(F.Id("k"), Num(2)))),
                "All variables are natural numbers. Choose K=1. For every k at least K, "
                + "substitute m=k-1 into the exact support cardinality and use the ordinary "
                + "binary bridge. Then (m+1)^2=k^2. This preserves the eventual quantifier "
                + "and supplies a threshold valid uniformly for all subsequent exponents.", Source),
            Paragraph(Text("The selected source assertion is the standalone eventual identity "
                + "a(2^k+1)=k^2 with its sufficiently-large lower-bound caveat. The proof here "
                + "establishes the exact threshold K=1 in the formal model. The other identities "
                + "listed by the source are separate assertions.")))));

    private static Formula CloseDefinition(string declaration, DescribeRole role, Formula statement)
    {
        if (role != DescribeRole.Definition) return statement;
        return declaration == "endpointOutput"
            ? Seq(Forall, Sp, Natural("m"), Comma, Natural("a"), Comma, Natural("c"), Comma, Sp, statement)
            : Seq(Forall, Sp, Natural(declaration == "binaryWord" || declaration == "distinctSelfShuffleCount" ? "n" : "m"), Comma, Sp, statement);
    }

    private static Formula Natural(string name) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, NaturalType()));

    private static Formula NaturalType() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula PairType(Formula m) =>
        Parenthesized(Seq(Call("Fin", Add(m, Num(1))), Sp, Times, Sp,
            Call("Fin", Add(m, Num(1)))));

    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);

    private static DocumentBlock.Describe Node(string declaration, string title,
        DescribeRole role, Formula statement, string prose,
        LibraryNoteRef? source = null) =>
        Describe.Lean(DescribeId.Create("endpoint-shuffle-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(CloseDefinition(declaration, role, statement))),
            source is null ? AssessedProvenance.FromRepo() : AssessedProvenance.FromRepo(source),
            Blocks(Paragraph(Text(prose))), role);
}
