using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class ScatteredPalindromeMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.";
    private const string Note = "D5/L/Words/mahalingampandoh2021scatteredpalindromes";

    public DocumentDefinition Create()
    {
        var w = F.Id("w"); var u = F.Id("u"); var n = F.Id("n"); var q = F.Id("q");
        var length = App(Q("List", "length"), w);
        var odd = Equal(App(Q("Nat", "mod"), n, D(2)), D(1));
        var upper = If(odd,
            Subtract(Multiply(D(3), Pow(D(2),
                Subtract(Div(Add(n, D(1)), D(2)), D(1)))), D(2)),
            Subtract(Pow(D(2), Add(Div(n, D(2)), D(1))), D(2)));
        var permitted = If(odd, Equal(q, Div(Add(n, D(1)), D(2))),
            Or(Equal(q, Div(n, D(2))), Equal(q, Add(Div(n, D(2)), D(1)))));
        var bound = Words(Leq(Call("sp", w), Call("maxSP", length)));
        var attainment = All("n", Nat, All("q", Nat, Imp(Leq(D(1), n),
            Imp(Call("permittedQ", n, q), Ex("w", Call("List", Nat),
                And(Equal(length, n), And(Equal(Call("alphabetSize", w), q),
                    Equal(Call("sp", w), Call("maxSP", n)))))))));
        var onlyWhen = Words(Imp(Leq(D(1), length),
            Imp(Equal(Call("sp", w), Call("maxSP", length)),
                Call("permittedQ", length, Call("alphabetSize", w)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The sharp maximum of distinct scattered palindromes and its alphabet sizes.",
            H("Maximum Number of Scattered Palindromes"), Blocks(
                Paragraph(Text("Words are List A, and List.Sublist is scattered containment. "
                    + "Finite sets remove duplicate embeddings. The empty subword is excluded. "
                    + "Nat.div is integer division, so Nat.div (n+1) 2 represents ⌈n/2⌉. "
                    + "Every subtraction is truncated natural subtraction.")),
                Definition("spal", "Distinct nonempty palindromic subsequences",
                    Words(Equal(Call("spal", w),
                        App(Q("Finset", "filter"), Lambda("u", Call("List", F.Id("A")),
                                And(NotEqual(u, EmptyList), Equal(App(Q("List", "reverse"), u), u))),
                            App(Q("List", "toFinset"), App(Q("List", "sublists"), w))))),
                    "Section 2, page 2: \"We denote by PAL(w) and SPAL(w), the set of all "
                    + "non-empty palindromic factors, and scattered palindromic subwords of w, "
                    + "respectively.\" List.sublists enumerates scattered subwords; List.toFinset "
                    + "counts each word once. A palindrome satisfies List.reverse u = u.",
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note))),
                Definition("sp", "Number of scattered palindromes", Words(
                    Equal(Call("sp", w), App(Q("Finset", "card"), Call("spal", w)))),
                    "Section 2, page 2: \"Also, P(w)=|PAL(w)| and SP(w)=|SPAL(w)|.\" "
                    + "Page 3: \"Throughout the paper, by the number of palindromic factors "
                    + "(resp. scattered palindromic subwords), we mean the number of non-empty "
                    + "distinct palindromic factors (resp. scattered palindromic subwords) in a word.\"",
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note))),
                Definition("alphabetSize", "Number of distinct letters", Words(
                    Equal(Call("alphabetSize", w),
                        App(Q("Finset", "card"), App(Q("List", "toFinset"), w)))),
                    "Section 2, page 2: \"Alph(w) denotes the set of all the subwords of w of "
                    + "length 1.\" List.toFinset contains exactly the letters that occur in w, "
                    + "so its cardinality is the source's q.",
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note))),
                Definition("maxSP", "The proposed sharp maximum", All("n", Nat,
                    Equal(Call("maxSP", n), upper)),
                    "The two printed cases are encoded literally with natural integer division.",
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)), true),
                Definition("permittedQ", "The extremal alphabet sizes", All("n", Nat,
                    All("q", Nat, Iff(Call("permittedQ", n, q), permitted))),
                    "The even case is a disjunction between two alphabet sizes.",
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)), true),
                Definition("claim", "Conjecture 5.6", Iff(Call("claim"),
                    And(bound, And(attainment, onlyWhen))),
                    "The encoding states a universal upper bound, attainment for every "
                    + "positive length and every permitted alphabet size, and necessity for "
                    + "every extremal nonempty word. Natural-number letters suffice for "
                    + "attainment; the bound and necessity quantify over every decidable alphabet.",
                    AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)), true),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("The conjecture holds"), StatementSource.FromAuthor(Disp(Call("claim"))),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                    Blocks(Paragraph(Text("Partition by the outer letter. A letter occurring "
                        + "once contributes one palindrome; a repeated letter contributes two "
                        + "plus the number of palindromes between its first and last occurrences. "
                        + "The convex endpoint matching estimate and the recurrence "
                        + "maxSP(n+2)=2 maxSP(n)+2 yield a residue bound by strong induction. "
                        + "Equality forces the residual length k to satisfy maxSP(k)=k and hence "
                        + "k≤2, and forces all repeated letters to occur exactly twice. "
                        + "For each permitted q, start with k distinct letters, where k is zero, "
                        + "one or two, and add r fresh matching outer pairs. The resulting word "
                        + "has length 2r+k, alphabet size r+k and count maxSP(2r+k). "
                        + "This constructs extremizers and restricts their alphabet sizes; it "
                        + "does not classify all extremal words or determine the maximum "
                        + "at every fixed alphabet size below half the length."))), DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("mahalingam-pandoh-2021-scattered-palindrome-maximum"),
                        ResolutionKind.Proved)))));
    }

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose, AssessedProvenance provenance,
        bool sourceQuotation = false) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance,
            Narrative(prose, sourceQuotation), DescribeRole.Definition);
    private static BlockSequence Narrative(string prose, bool sourceQuotation) => sourceQuotation
        ? Blocks(
            Paragraph(Text("Conjecture 5.6, page 18:")),
            Paragraph(Text("“The maximum number of scattered palindromic subwords in a word of length n is")),
            Paragraph(Text("3(2^{⌈n/2⌉−1})−2, if n is odd,")),
            Paragraph(Text("2^{n/2+1}−2, if n is even.")),
            Paragraph(Text("and this bound is achieved only when")),
            Paragraph(Text("q =")),
            Paragraph(Text("⌈n/2⌉, if n is odd")),
            Paragraph(Text("n/2 and n/2+1, if n is even.”")),
            Paragraph(Text(prose)))
        : Blocks(Paragraph(Text(prose)));
    private static Formula Nat => F.Id("Nat");
    private static Formula EmptyList => Seq(OpenBracket, CloseBracket);
    private static Formula Words(Formula body) => All("A", F.Id("Type"),
        Seq(OpenBracket, Call("DecidableEq", F.Id("A")), CloseBracket, Comma, Sp,
            All("w", Call("List", F.Id("A")), body)));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, F.Id(name));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Div(Formula a, Formula b) => App(Q("Nat", "div"), a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Lambda(string x, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(x), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(F.Id("if"), Sp, condition, Sp, F.Id("then"), Sp, yes,
            Sp, F.Id("else"), Sp, Parenthesized(no));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
