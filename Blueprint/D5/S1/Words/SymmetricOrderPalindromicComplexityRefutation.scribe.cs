using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class SymmetricOrderPalindromicComplexityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.";
    private const string Note = "D5/L/Words/ferenczizamboni2025clustering";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-letter path language has symmetric orders and no connection, but only three palindromes of length three.",
        H("Transient Letters and Palindromic Complexity"),
        Blocks(
            Paragraph(Text(
                "Words are finite lists over Fin k. A permutation sigma gives the departure "
                + "order by sigma a < sigma b and the arrival order by sigma b < sigma a. "
                + "Thus the two orders are strict, total and symmetric. Section 2, page 5: "
                + "\"A pair of orders (<D, <A) is symmetric if <A is the reverse of <D, "
                + "i.e. a <A b if and only if b <D a for all distinct letters a, b ∈ A.\"")),
            Definition("IsFactorial", "Factors remain in the language", Language(
                Equivalent(Call("IsFactorial", K),
                    All("w", Words, Imp(Member(W, K), All("u", Words,
                        Imp(App(Q("List", "IsInfix"), F.Id("u"), W), Member(F.Id("u"), K))))))),
                "Section 1, page 4: \"By a language L over A we mean a factorial language: "
                + "a collection of sets (Ln)n≥0 where the only element of L0 is the empty word ε, "
                + "and where each Ln for n ≥ 1 consists of words of length n, such that each "
                + "v ∈ Ln+1 can be written in the form v = au = u′b with a, b ∈ A and u, u′ ∈ Ln.\" "
                + "IsFactorial encodes closure under every contiguous factor using List.IsInfix. "
                + "The counterexample contains the empty word; UsesAllLetters fixes its alphabet."),
            Definition("IsExtendable", "Two-sided extendability", Language(
                Equivalent(Call("IsExtendable", K), All("w", Words, Imp(Member(W, K),
                    And(Ex("a", Letters, Member(Cons(F.Id("a"), W), K)),
                        Ex("b", Letters, Member(Append(W, Single(F.Id("b"))), K))))))),
                "Section 1, page 4: \"Except when otherwise mentioned, all our languages are "
                + "tacitly assumed to be extendable: for each v ∈ Ln there exists a,b ∈ A "
                + "with av,vb ∈ Ln+1.\" Left extension is List.cons; right extension appends a singleton."),
            Definition("UsesAllLetters", "The alphabet has k letters", Language(
                Equivalent(Call("UsesAllLetters", K), All("a", Letters, Member(Single(F.Id("a")), K)))),
                "Conjecture 1, page 14: \"A language on k letters satisfying a symmetric order "
                + "condition and with no connection has palindromic complexity 1 for n even, k "
                + "for n odd.\" Every element of Fin k occurs as a singleton. Consequently the "
                + "alphabet has exactly k letters, rather than merely being contained in Fin k."),
            Definition("SymOrderCondition", "The symmetric order condition", OrderedLanguage(
                Equivalent(Call("SymOrderCondition", K, Sigma),
                    All("a", Letters, All("b", Letters, All("c", Letters, All("d", Letters,
                        All("x", Words,
                            Imp(Member(Bilateral(F.Id("a"), F.Id("x"), F.Id("b")), K),
                                Imp(Member(Bilateral(F.Id("c"), F.Id("x"), F.Id("d")), K),
                                    Imp(NotEqual(F.Id("a"), F.Id("c")),
                                        Imp(NotEqual(F.Id("b"), F.Id("d")),
                                            Equivalent(Less(SigmaAt("c"), SigmaAt("a")),
                                                Less(SigmaAt("b"), SigmaAt("d")))))))))))))),
                "Definition 6, page 6: \"A language L (extendable or not) satisfies the order "
                + "condition for the pair of orders (<D,<A) if whenever axb, cxd ∈ L with "
                + "a, b,c,d ∈ A, x ∈ A* (possibly empty), a ≠ c and b ≠ d, then a <A c "
                + "if and only if b <D d. The order condition is called the symmetric order "
                + "condition if the pair of orders (<D,<A) is symmetric.\" The middle word x "
                + "may be empty. The reversed arrival order explains the comparison sigma c < sigma a."),
            Definition("IsBispecial", "Bispecial words", Language(All("w", Words,
                Equivalent(Call("IsBispecial", K, W),
                    And(Ex("a1", Letters, Ex("a2", Letters,
                            And(NotEqual(F.Id("a1"), F.Id("a2")),
                                And(Member(Cons(F.Id("a1"), W), K), Member(Cons(F.Id("a2"), W), K))))),
                        Ex("b1", Letters, Ex("b2", Letters,
                            And(NotEqual(F.Id("b1"), F.Id("b2")),
                                And(Member(Append(W, Single(F.Id("b1"))), K),
                                    Member(Append(W, Single(F.Id("b2"))), K))))))))),
                "Section 1, page 4: \"A word w in L is right special (resp. left special) "
                + "if it has more than one right extension wx (resp. left extension xw) in L, "
                + "with x in A. If w is both right special and left special, then w is bispecial.\" "
                + "The two existential pairs state that the one-letter extensions are distinct. "
                + "For a factorial language these extensions also imply w ∈ L."),
            Definition("NoConnection", "No connection", OrderedLanguage(
                Equivalent(Call("NoConnection", K, Sigma), All("w", Words,
                    Imp(Call("IsBispecial", K, W),
                        All("a", Letters, All("ap", Letters, All("b", Letters, All("bp", Letters,
                            Imp(Consecutive("ap", "a"), Imp(Consecutive("b", "bp"),
                                Imp(Member(Bilateral(F.Id("a"), W, F.Id("b")), K),
                                    Imp(Member(Bilateral(F.Id("ap"), W, F.Id("bp")), K),
                                        Imp(Not(Member(Bilateral(F.Id("a"), W, F.Id("bp")), K)),
                                            Imp(Not(Member(Bilateral(F.Id("ap"), W, F.Id("b")), K)),
                                                F.Id("False"))))))))))))))),
                "Definition 7, page 6: \"If a language L on an alphabet A satisfies the order "
                + "condition for (<D,<A), a bispecial word w has a connection if there are "
                + "letters a <A a′, consecutive in the order <A, letters b <D b′, consecutive "
                + "in the order <D, such that awb and a′wb′ are in L, and neither awb′ nor "
                + "a′wb is in L.\" The letters ap and bp encode a′ and b′. Consecutiveness "
                + "means strict comparison with no intervening letter. Arrival consecutiveness "
                + "is reversed, so sigma ap < sigma a; departure consecutiveness is sigma b < sigma bp."),
            Definition("palComplexity", "Palindromic complexity", Language(All("n", Nat,
                Equal(Call("palComplexity", K, F.Id("n")),
                    App(Q("Set", "ncard"), Seq(OpenBrace, W, Colon, Sp, Words, Sp, Mid, Sp,
                        And(Member(W, K), And(Equal(App(Q("List", "length"), W), F.Id("n")),
                            Equal(App(Q("List", "reverse"), W), W))), CloseBrace))))),
                "Introduction, page 3: \"We give also some estimates on the palindromic complexity of L, i.e., the number of palindromes in L of each given length n.\" "
                + "A palindrome satisfies List.reverse w = w. Set.ncard counts the set of "
                + "such words of length n; this set is finite because Fin k is finite. The empty "
                + "word contributes one at length zero whenever it belongs to the language."),
            Definition("claim", "Conjecture 1", Equivalent(Call("claim"),
                OrderedLanguage(Imp(Call("IsFactorial", K), Imp(Call("IsExtendable", K),
                    Imp(Call("UsesAllLetters", K), Imp(Call("SymOrderCondition", K, Sigma),
                        Imp(Call("NoConnection", K, Sigma), All("n", Nat,
                            Equal(Call("palComplexity", K, F.Id("n")),
                                Seq(F.Id("if"), Sp, Call("Even", F.Id("n")), Sp, F.Id("then"),
                                    Sp, D(1), Sp, F.Id("else"), Sp, F.Id("k"))))))))))),
                "Section 4, Conjecture 1, page 14: \"A language on k letters satisfying a "
                + "symmetric order condition and with no connection has palindromic complexity "
                + "1 for n even, k for n odd.\" The encoding quantifies over every natural k, "
                + "every K : Set (List (Fin k)), every sigma : Equiv.Perm (Fin k), and every "
                + "natural n, including zero. The hypotheses state factoriality, two-sided "
                + "extendability, use of all letters, the symmetric order condition, and absence "
                + "of connections. No recurrence or closure under reversal is assumed."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A four-letter counterexample"),
                StatementSource.FromAuthor(Disp(Not(Call("claim")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text(
                    "Use the graph on Fin 4 with edges 0 → 3, 1 → 3, 2 → j for every j, "
                    + "and 3 → 0. Its finite paths form a factorial language containing the "
                    + "empty word. Vertex 2 precedes every vertex, and every vertex has a "
                    + "successor, so the language extends on both sides and uses all four "
                    + "letters. Distinct incoming edges force their common target into {0,3}; "
                    + "subsequent vertices stay in the deterministic two-cycle. Hence no "
                    + "nonempty word is bispecial. The empty word satisfies the symmetric "
                    + "order condition and has no connection, as verified from the edge rows. "
                    + "The palindromes of length three are exactly [2,2,2], [0,3,0] and "
                    + "[3,0,3]. Thus palComplexity at three is three, while the conjecture "
                    + "requires four. The source vertices 1,2,3,4 correspond to 0,1,2,3."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ferenczi-zamboni-2025-palindromic-complexity-no-connection"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text(text))));

    private static Formula Nat => F.Id("Nat");
    private static Formula K => F.Id("K");
    private static Formula W => F.Id("w");
    private static Formula Sigma => F.Id("sigma");
    private static Formula Letters => Call("Fin", F.Id("k"));
    private static Formula Words => Call("List", Letters);
    private static Formula Language(Formula body) => All("k", Nat, All("K", Call("Set", Words), body));
    private static Formula OrderedLanguage(Formula body) =>
        Language(All("sigma", App(Q("Equiv", "Perm"), Letters), body));
    private static Formula SigmaAt(string x) => App(Sigma, F.Id(x));
    private static Formula Consecutive(string x, string y) =>
        And(Less(SigmaAt(x), SigmaAt(y)), All("z", Letters,
            Not(And(Less(SigmaAt(x), SigmaAt("z")), Less(SigmaAt("z"), SigmaAt(y))))));
    private static Formula Bilateral(Formula a, Formula w, Formula b) => Cons(a, Append(w, Single(b)));
    private static Formula Cons(Formula a, Formula w) => App(Q("List", "cons"), a, w);
    private static Formula Single(Formula a) => Seq(OpenBracket, a, CloseBracket);
    private static Formula Append(Formula w, Formula v) => Parenthesized(Seq(w, Plus, Plus, v));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, F.Id(name));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? F.Id(name) : new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
