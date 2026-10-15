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
            Describe.Lean(
                DescribeId.Create("factor-length"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.factor_len"),
                H("Exact factor length"), StatementSource.FromAuthor(WindowSupplier("factor_len")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every alphabet size m, every function x from the naturals to Fin m, and all natural i and n, the length-n factor of x at i has length n. This identity gives the lengths of finite prefixes in periodic intervals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-iterate-prefix"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.iterate_prefix"),
                H("Nested actual iterates"), StatementSource.FromAuthor(WindowSupplier("iterate_prefix")),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every order m at least two and natural k at most t, the kth iterate on zero is a prefix of the tth iterate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-iterate-growth"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.iterate_growth"),
                H("Unbounded actual image lengths"), StatementSource.FromAuthor(WindowSupplier("iterate_growth")),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every order m at least two and every natural k, the kth iterate on zero has length at least k+1. Each substitution step adds a nonempty image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-word-eq-iterate"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.word_eq_iterate"),
                H("Compatible readings of the actual word"), StatementSource.FromAuthor(WindowSupplier("word_eq_iterate")),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every order m at least two, every k and every n less than the kth image length, the actual letter at n equals the letter at n of that iterate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-factor-get"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.factor_get"),
                H("The exact letter of a factor"), StatementSource.FromAuthor(WindowSupplier("factor_get")),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For any order m, any function x from the naturals to Fin m, and naturals i,n,j with j<n, the jth letter of the length-n factor of x at i equals x(i+j)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boundary-window"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.boundary_window"),
                H("Every natural start has a source block"), StatementSource.FromAuthor(ConverseStatement("boundary_window")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m at least two and every natural q, some i satisfies boundary(i) at most q and q less than boundary(i+1). The original strict and unbounded block construction includes q equal to zero. Images have at most two letters, so the converse has exactly the boundary offset zero or one cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("factor-add"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.factor_add"),
                H("Exact contiguous factor concatenation"), StatementSource.FromAuthor(ConverseStatement("factor_add")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every alphabet size, every infinite word x and all natural i,n,t, factor(x,i,n+t) is factor(x,i,n) followed by factor(x,i+n,t). The converse uses this original identity to choose the next source letter at the end of a complete predecessor window."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("occ-cons"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.occ_cons"),
                H("Exact first-letter removal"), StatementSource.FromAuthor(ConverseStatement("occ_cons")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual source order at least two, letter a, list s and natural q, occurrence of a followed by s at q is equivalent to word(q) equal to a and occurrence of s at q+1. This original bridge removes the first output zero in both offset-one cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("t-head"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciSentinelDesubstitution.t_head"),
                H("The original sentinel starts in zero"), StatementSource.FromAuthor(ConverseStatement("t_head")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual source order at least two and every source list s, T(s) is zero followed by a list. This includes empty s. It is the original first-letter supplier for additive count cancellation in the clipped transport."))),
                DescribeRole.Theorem),
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

    private static Formula ConverseStatement(string name)
    {
        var m = F.Id("m"); var n = F.Id("n"); var k = F.Id("k");
        var q = F.Id("q"); var i = F.Id("i"); var t = F.Id("t");
        var r = F.Id("r"); var s = F.Id("s"); var a = F.Id("a");
        var x = F.Id("x"); var count = F.Id("count");
        Formula ns = CFCall("S", m, k);
        Formula si = CFCall("sentinelIter", m, k);
        Formula rho = CFCall("ncard", CFCall("parikhImage", m, n));
        Formula minimum = CFEq(rho, m);
        Formula sentinel = CFEx("k", CFN(), CFEq(n, ns));
        Formula periodic = CFEx("k", CFN(), CFEq(CFCall("fullGreedy", m, n),
            CFCall("periodicDigits", m, k)));
        Formula body = name switch
        {
            "boundary_window" => CFAll("q", CFN(), CFEx("i", CFN(),
                CFAnd(CFLe(CFCall("boundary", m, i), q),
                    CFLt(q, CFCall("boundary", m, CFAdd(i, F.D(1))))))),
            "t_head" => CFAll("s", CFCall("List", CFCall("Fin", m)),
                CFEx("v", CFCall("List", CFCall("Fin", m)),
                    CFEq(CFCall("T", m, s), CFCall("cons", F.D(0), F.Id("v"))))),
            "occ_cons" => CFAll("a", CFCall("Fin", m),
                CFAll("s", CFCall("List", CFCall("Fin", m)), CFAll("q", CFN(),
                    CFIff(CFCall("Occ", m, CFCall("cons", a, s), q),
                        CFAnd(CFEq(CFCall("word", m, q), a),
                            CFCall("Occ", m, s, CFAdd(q, F.D(1)))))))),
            "factor_add" => CFAll("x", Parenthesized(new Formula.TypeArrow(CFN(), CFCall("Fin", m))),
                CFAll("i", CFN(), CFAll("n", CFN(), CFAll("t", CFN(),
                    CFEq(CFCall("factor", x, i, CFAdd(n, t)),
                        CFCall("append", CFCall("factor", x, i, n),
                            CFCall("factor", x, CFAdd(i, n), t))))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name)),
        };
        Formula bound = name == "uniform_minimum_characterization"
            ? CFAnd(CFLe(F.D(2), m), CFLe(F.D(5), m)) : CFLe(F.D(2), m);
        bool unrestricted = name is "star" or "star_injective" or "factor_add";
        return F.Disp(CFAll("m", CFN(), unrestricted ? body : CFImp(bound, body)));
    }

    private static Formula CFN() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula CFCall(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula CFAll(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula CFEx(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula CFEq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula CFLe(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula CFLt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula CFAdd(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula CFAnd(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula CFImp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula CFIff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula WindowSupplier(string name)
    {
        Formula m = F.Id("m"), k = F.Id("k"), t = F.Id("t"), n = F.Id("n");
        Formula i = F.Id("i"), j = F.Id("j"), x = F.Id("x");
        Formula alphabet = WC("Fin", m);
        Formula P(Formula a) => WC("image", WC("phi", m), a, WC("zero", m));
        Formula body = name switch
        {
            "iterate_prefix" => WA("k", WN(), WA("t", WN(), WI(WL(k, t),
                WC("IsPrefix", P(k), P(t))))),
            "iterate_growth" => WA("k", WN(), WL(WP(k, F.D(1)), WC("length", P(k)))),
            "word_eq_iterate" => WA("k", WN(), WA("n", WN(),
                WI(WT(n, WC("length", P(k))), WQ(WC("word", m, n), WC("getElem", P(k), n))))),
            "factor_get" => WA("x", Parenthesized(new Formula.TypeArrow(WN(), alphabet)),
                WA("i", WN(), WA("n", WN(), WA("j", WN(), WI(WT(j, n),
                    WQ(WC("getElem", WC("factor", x, i, n), j),
                        new Formula.Apply(x, [WP(i, j)]))))))),
            "factor_len" => WA("x", Parenthesized(new Formula.TypeArrow(WN(), alphabet)),
                WA("i", WN(), WA("n", WN(),
                    WQ(WC("length", WC("factor", x, i, n)), n)))),
            _ => throw new ArgumentOutOfRangeException(nameof(name)),
        };
        return F.Disp(WA("m", WN(), name == "factor_get" || name == "factor_len"
            ? body : WI(WL(F.D(2), m), body)));
    }

    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);

    private static Formula WN() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula WC(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula WA(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula WQ(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula WL(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula WT(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula WP(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula WI(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

}
