using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class MBonacciSentinelDesubstitutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/MBonacciSentinelDesubstitution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual m-bonacci word admits unique sentinel desubstitution and strict fully "
            + "right-special descent for every order at least two.",
        H("Sentinel Desubstitution of the m-bonacci Word"),
        Blocks(
            Paragraph(Text("The alphabet is Fin m, with m at least two. Every occurrence is a "
                + "contiguous list factor at a natural starting position. Position zero and the "
                + "empty source word are included. No recurrence or fixed-word assumption is "
                + "needed: the infinite word is constructed from the nested finite iterates.")),
            Def("zero", "zero", "The zero letter",
                "The order bound supplies the positivity needed to form the zero of Fin m."),
            Def("rot", "rot", "Cyclic successor",
                "Successor sends a to a+1 below m and sends m-1 to zero. It is a permutation "
                + "of the alphabet; its value is (a+1) modulo m."),
            Def("phi", "phi", "The literal substitution",
                "Every nonterminal letter a has image [0,a+1], and the terminal letter m-1 "
                + "has image [0]. Thus every image is nonempty, begins in zero and has length "
                + "at most two. The generic substitution and finite iterate operators are reused."),
            Def("word", "word", "The actual infinite word",
                "Letter n is read at position n of the (n+1)st iterate on zero. The iterates "
                + "are nested: the next iterate is the current iterate followed by the iterate "
                + "on one. The latter is nonempty, so the kth iterate has length at least k+1. "
                + "Comparing both readings in a common longer iterate proves compatibility."),
            Def("boundary", "boundary", "True block boundaries",
                "The boundary B(i) is the length of the substituted prefix of i source "
                + "letters. It also equals the sum of their individual image lengths."),
            Def("Occ", "occ", "Actual occurrence",
                "Occ(s,q) asserts equality of s with the supplied length-|s| list factor "
                + "starting at q. No bounded prefix replaces the set of natural starts."),
            Def("T", "sentinel", "Reserved final zero",
                "T(s) is the substituted source word followed by one zero. This last zero "
                + "marks the next block and is reserved rather than decoded as a source letter."),
            Def("FRS", "frs", "Fully right-special factors",
                "A word is fully right-special when appending each alphabet letter gives "
                + "an actual occurrence, with the starting position allowed to depend on the letter."),
            Thm("actual_word_laws", "actual-word-laws", "Closed word and block laws",
                "Every finite iterate is an exact prefix of the constructed word. Applying "
                + "the substitution to a source prefix gives another exact prefix. Cancellation "
                + "between successive prefixes yields the block at B(i). Positive image lengths "
                + "make B strictly increasing, with B(0)=0 and the stated sum formula. A nonzero "
                + "letter is the second position of a two-letter image; the next position is zero."),
            Thm("zero_iff_unique_boundary", "zero-boundary", "Zeros identify unique boundaries",
                "Every natural position lies between two successive boundaries. The only "
                + "possible interior position is the nonzero second letter of a two-letter "
                + "image. Hence zero positions are precisely boundaries, and strict growth "
                + "gives uniqueness, including the boundary at zero."),
            Thm("occurrence_transport", "transport", "Transport of actual occurrences",
                "An occurrence of s at i lifts to the image and its sentinel at B(i). "
                + "For nonempty s, removing the initial zero gives the image tail at B(i)+1. "
                + "The first two transports also apply to the empty word."),
            Thm("sentinel_occurrence_iff", "sentinel-occurrence", "Exact sentinel occurrence bridge",
                "The leading zero identifies a boundary. The next letter is the cyclic "
                + "successor of the source letter, including zero for the terminal letter. "
                + "Injectivity of cyclic successor identifies that source letter, and induction "
                + "continues at the next boundary. The empty case is the single zero sentinel."),
            Thm("right_extension_occurrence_iff", "extension-occurrence",
                "Exact right-extension bridge",
                "After T(s), the next position is one past B(i+|s|), so its letter is the "
                + "cyclic successor of the next source letter. This proves both directions "
                + "for every right extension using the same source word and boundary map."),
            Thm("common_unique_preimage", "common-preimage", "A common unique shorter preimage",
                "For an actual nonempty factor beginning and ending in zero, its two endpoints "
                + "are boundaries B(i) and B(j). Take the source factor from i to j. Substitution "
                + "transport and the endpoint length identity give r=T(s). Comparing the first "
                + "two letters of two sentinel encodings and then cancelling their common image "
                + "proves uniqueness. Nonerasing images and the extra sentinel imply |s|<|r|. "
                + "Adjacent zeros decode m-1; a zero, a nonzero b and the following zero decode "
                + "b-1. The single zero has the empty preimage."),
            Thm("fully_right_special_descent", "frs-descent", "Strict fully right-special descent",
                "If a nonempty fully right-special factor ended in a nonzero letter, adjacency "
                + "would force its next letter to be zero, contradicting its extension by one. "
                + "It therefore ends in zero. Its unique shorter preimage is fully right-special: "
                + "each extension by rot(b) descends to an extension by b. The same preimage "
                + "satisfies both all-start occurrence equivalences, with no extra end-zero premise."),
            Paragraph(Text("These are structural laws of the actual word. They do not determine "
                + "its abelian complexity or characterize greedy numeration digits.")))));

    private static DocumentBlock Def(string name, string id, string title, string prose) =>
        Node(name, id, title, prose, DescribeRole.Definition);

    private static DocumentBlock Thm(string name, string id, string title, string prose) =>
        Node(name, id, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Node(string name, string id, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(FormulaFor(name)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula FormulaFor(string name)
    {
        Formula s = F.Id("s"), r = F.Id("r"), q = F.Id("q"), i = F.Id("i");
        Formula a = F.Id("a"), b = F.Id("b"), k = F.Id("k"), n = F.Id("n");
        Formula image = Call("image", F.Id("phi"), k, D(0));
        Formula shortPreimage = And(Eq(r, Sent(s)), Lt(Len(s), Len(r)));
        Formula occurrenceBridge = Iff(Occ(r, q),
            Ex("i", N(), And(Eq(q, Bound(i)), Occ(s, i))));
        Formula extensionBridge = Iff(Occ(Append(r, Single(Call("rot", b))), q),
            Ex("i", N(), And(Eq(q, Bound(i)), Occ(Append(s, Single(b)), i))));
        Formula body = name switch
        {
            "zero" => Eq(Call("val", F.Id("zero")), D(0)),
            "rot" => All("a", Alphabet(), Eq(Call("val", Call("rot", a)),
                Call("mod", Add(Call("val", a), D(1)), F.Id("m")))),
            "phi" => All("a", Alphabet(), And(
                Imp(Lt(Add(Call("val", a), D(1)), F.Id("m")),
                    Eq(Call("phi", a), List(D(0), Add(Call("val", a), D(1))))),
                Imp(Eq(Add(Call("val", a), D(1)), F.Id("m")),
                    Eq(Call("phi", a), Single(D(0)))))),
            "word" => All("n", N(), Eq(Word(n), Call("getElem",
                Call("image", F.Id("phi"), Add(n, D(1)), D(0)), n))),
            "boundary" => All("i", N(), Eq(Bound(i), Len(Subst(Factor(D(0), i))))),
            "Occ" => All("s", Words(), All("q", N(),
                Iff(Occ(s, q), Eq(Factor(q, Len(s)), s)))),
            "T" => All("s", Words(), Eq(Sent(s), Append(Subst(s), Single(D(0))))),
            "FRS" => All("r", Words(), Iff(Call("FRS", r),
                All("a", Alphabet(), Ex("q", N(), Occ(Append(r, Single(a)), q))))),
            "zero_iff_unique_boundary" => All("q", N(), Iff(Eq(Word(q), D(0)),
                Unique("i", N(), Eq(q, Bound(i))))),
            "sentinel_occurrence_iff" => All("s", Words(), All("q", N(),
                Iff(Occ(Sent(s), q), Ex("i", N(), And(Eq(q, Bound(i)), Occ(s, i)))))),
            "right_extension_occurrence_iff" => All("s", Words(), All("b", Alphabet(),
                All("q", N(), Iff(Occ(Append(Sent(s), Single(Call("rot", b))), q),
                    Ex("i", N(), And(Eq(q, Bound(i)), Occ(Append(s, Single(b)), i))))))),
            "common_unique_preimage" => All("r", Words(), Imp(Ne(r, List()),
                Imp(Ex("q", N(), Occ(r, q)), Imp(Eq(Call("headopt", r), Call("some", D(0))),
                    Imp(Eq(Call("lastopt", r), Call("some", D(0))),
                        Unique("s", Words(), shortPreimage)))))),
            "fully_right_special_descent" => All("r", Words(), Imp(Ne(r, List()),
                Imp(Eq(Call("headopt", r), Call("some", D(0))), Imp(Call("FRS", r),
                    Unique("s", Words(), And(Eq(r, Sent(s)), And(Lt(Len(s), Len(r)),
                        And(Call("FRS", s), And(All("q", N(), occurrenceBridge),
                            All("b", Alphabet(), All("q", N(), extensionBridge))))))))))),
            "occurrence_transport" => All("s", Words(), All("i", N(), Imp(Occ(s, i),
                And(Occ(Subst(s), Bound(i)), And(Occ(Sent(s), Bound(i)),
                    Imp(Ne(s, List()), Occ(Call("tail", Subst(s)), Add(Bound(i), D(1))))))))),
            "actual_word_laws" => Conj(
                All("k", N(), Eq(Factor(D(0), Len(image)), image)),
                Call("StrictMono", F.Id("boundary")), Eq(Bound(D(0)), D(0)),
                All("i", N(), Eq(Bound(i), SumOver("h", Call("range", i),
                    Len(Call("phi", Word(F.Id("h"))))))),
                All("i", N(), Eq(Factor(Bound(i), Len(Call("phi", Word(i)))),
                    Call("phi", Word(i)))),
                All("q", N(), Imp(Ne(Word(q), D(0)), Eq(Word(Add(q, D(1))), D(0)))),
                All("a", Alphabet(), Eq(Call("val", Call("rot", a)),
                    Call("mod", Add(Call("val", a), D(1)), F.Id("m"))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name)),
        };
        return Disp(All("m", N(), Imp(Leq(D(2), F.Id("m")), body)));
    }

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Alphabet() => Call("Fin", F.Id("m"));
    private static Formula Words() => Call("List", Alphabet());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Word(Formula n) => Call("word", n);
    private static Formula Bound(Formula i) => Call("boundary", i);
    private static Formula Factor(Formula q, Formula n) => Call("factor", F.Id("word"), q, n);
    private static Formula Len(Formula s) => Call("length", s);
    private static Formula Subst(Formula s) => Call("subst", F.Id("phi"), s);
    private static Formula Sent(Formula s) => Call("T", s);
    private static Formula Occ(Formula s, Formula q) => Call("Occ", s, q);
    private static Formula List(params Formula[] entries)
    {
        var parts = new System.Collections.Generic.List<Formula> { OpenBracket };
        for (int j = 0; j < entries.Length; j++)
        {
            if (j > 0) parts.Add(Comma);
            parts.Add(entries[j]);
        }
        parts.Add(CloseBracket);
        return Seq([.. parts]);
    }
    private static Formula Single(Formula a) => List(a);
    private static Formula Append(Formula s, Formula t) => Call("append", s, t);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Unique(string x, Formula domain, Formula body) =>
        Seq(Exists, Bang, Sp, F.Id(x), Colon, domain, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conj(params Formula[] items)
    {
        Formula result = items[^1];
        for (int j = items.Length - 2; j >= 0; j--) result = And(items[j], result);
        return result;
    }
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula SumOver(string x, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(x), Sp, InMacro, Sp, domain), Sp,
            Seq(Open, body, Close));
}
