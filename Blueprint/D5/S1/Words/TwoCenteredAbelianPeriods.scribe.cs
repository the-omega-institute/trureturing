using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class TwoCenteredAbelianPeriodsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/TwoCenteredAbelianPeriods.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/avgustinovich2012critical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two centered abelian period lengths force ordinary periodicity.",
        H("Two centered abelian periods"),
        Blocks(
            Node("central-abelian-power", "Centered abelian powers", "CentralAbelianPower",
                CentralFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Section 2.2, p. 6: “Two words u and v in Σ∗ are abelian equivalent if and only if "
                + "|u|ₐ = |v|ₐ for all a ∈ Σ.” “An abelian k-power is a non-empty word of the form "
                + "u = v₁v₂…v_k where the words vᵢ are pairwise abelian equivalent. In this case "
                + "we refer to |v₁| as the length of an abelian period of u (or briefly period).” "
                + "“Let w be a biinfinite word over an alphabet Σ. For integer i, by a position "
                + "i in a word w we mean a position between wᵢ and wᵢ₊₁.” "
                + "“for every i there exists l′ ≤ l such that w_{i−l′k+1} … w_{i+l′k} "
                + "is an abelian 2k-power.” The fixed-length predicate displays this centered "
                + "factor at a specified period length l. The integer-indexed word takes values in Fin r. The factor from i−lk+1 "
                + "through i+lk consists of 2k nonempty blocks of length l. "
                + "Each block has the same letterCount as the first block. All arithmetic "
                + "in the starting position is integer arithmetic."),
            Node("ordinary-periodicity", "Ordinary periodicity", "Periodic",
                PeriodicFormula(), DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Section 2.1, p. 4: “We say that a biinfinite word w is periodic, if "
                + "there exists a finite word v such that w = v^ℤ.” The positive-period encoding "
                + "uses a natural period p: "
                + "w(n+p)=w(n) for every integer n."),
            Node("two-length-question", "The negative answer to Open problem 6.2", "claim",
                Disp(IffBody(X("claim"), ClaimBody())), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source), QuestionText()),
            Node("two-length-periodicity", "Two lengths force periodicity", "result",
                Disp(ClaimBody()), DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "Every word satisfying the two-length alternative is periodic. "
                + "The middle two blocks reduce each centered power to an abelian square. "
                + "For each letter, the mixed forward difference of its cumulative count "
                + "vanishes: an exact square identity makes a bounded integer flux antitone, "
                + "and a bounded coboundary on both tails forces the flux to be zero. "
                + "When both lengths are positive, the proof gives their least common multiple "
                + "as a period. A zero length is excluded by the nonempty-block condition. "
                + "No earlier answer was identified in the bounded literature screen; "
                + "completeness of that screen remains unverified.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("akp-2012-two-centered-abelian-periods"),
                    ResolutionKind.Proved)))));

    private static string QuestionText() =>
        "Open problem 6.2, p. 14: “Let k be an integer. Does there exist a non-periodic word "
        + "w and integers l₁, l₂, such that w contains a central abelian 2k-power of length l₁ "
        + "or l₂ at every position?” “Notice that the construction from Theorem 3.2 gives "
        + "an example of such a word using three periods. One period trivially implies "
        + "periodicity. So two periods is an open question.” The proposition answers no "
        + "for every positive k and every finite alphabet Fin r, with integer-indexed words "
        + "and positive block lengths.";

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula CentralFormula()
    {
        var equalCounts = All("a", Call("Fin", X("r")),
            Eq(CountAt(Add(Start(), Mul(Cast(X("j")), Cast(X("l"))))), CountAt(Start())));
        var body = And(Lt(D(0), X("l")),
            All("j", X("Nat"), Imp(Lt(X("j"), Mul(D(2), X("k"))), equalCounts)));
        var equality = IffBody(Call("CentralAbelianPower", X("w"), X("k"), X("l"), X("i")), body);
        return Disp(All("r", X("Nat"),
            All("w", Arrow(X("Int"), Call("Fin", X("r"))),
                All("k", X("Nat"), All("l", X("Nat"), All("i", X("Int"), equality))))));
    }

    private static Formula Start() => Add(
        Sub(X("i"), Mul(Cast(X("l")), Cast(X("k")))), D(1));

    private static Formula CountAt(Formula start) => App(
        Qualified("AbelianBorderQuestionDefs", "letterCount"),
        App(Qualified("List", "ofFn"),
            Seq(Keyword("fun"), Sp,
                Parenthesized(Seq(X("t"), Colon, Sp, Call("Fin", X("l")))),
                Sp, Mapsto, Sp, Call("w", Add(start, Cast(Call("val", X("t"))))))),
        X("a"));

    private static Formula PeriodicFormula()
    {
        var body = Ex("p", X("Nat"), And(Lt(D(0), X("p")),
            All("n", X("Int"), Eq(Call("w", Add(X("n"), Cast(X("p")))), Call("w", X("n"))))));
        return Disp(All("r", X("Nat"),
            All("w", Arrow(X("Int"), Call("Fin", X("r"))),
                IffBody(Call("Periodic", X("w")), body))));
    }

    private static Formula ClaimBody()
    {
        var alternative = All("i", X("Int"),
            Or(Call("CentralAbelianPower", X("w"), X("k"), X("l1"), X("i")),
               Call("CentralAbelianPower", X("w"), X("k"), X("l2"), X("i"))));
        var implication = Imp(alternative, Call("Periodic", X("w")));
        var lengths = All("l1", X("Nat"), All("l2", X("Nat"), implication));
        var words = All("r", X("Nat"),
            All("w", Arrow(X("Int"), Call("Fin", X("r"))), lengths));
        return All("k", X("Nat"), Imp(Le(D(1), X("k")), words));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => App(X(name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula Keyword(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Cast(Formula body) => Parenthesized(Seq(body, Colon, Sp, X("Int")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffBody(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
