using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class RowlandSistosBarronRankSequencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/RowlandSistosBarronRankSequences.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/rowlandsistosbarron2025powers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parameter-dependent coefficient cancellation gives infinitely many rank sequences.",
        H("Infinitely Many Rank Sequences of Initial Rank Three"),
        Blocks(
            Node("recurrence", "An eventual recurrence", "HasRecurrence", RecurrenceFormula(),
                "Section 2, page 3: “First, a constant-recursive sequence is one which satisfies "
                + "a recurrence equation of the form s(n + r) = c_{r−1} s(n + r − 1) + · · · + "
                + "c_1 s(n + 1) + c_0 s(n). for any sufficiently large n, where the coefficients "
                + "(c_{r−1}, . . . , c_0) are all constants and c_0 ≠ 0.” "
                + "Here s takes integer values, the coefficients are rational, E.coeffs i is c_i, "
                + "and E.IsSolution applies to the tail n ↦ s(n + N). At order zero, the condition "
                + "on coefficients is vacuous and the sequence is eventually zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("constant-recursive", "Constant-recursive integer sequences", "IsConstantRecursive",
                ConstantRecursiveFormula(),
                "Section 2, page 3: “First, a constant-recursive sequence is one which satisfies "
                + "a recurrence equation of the form s(n + r) = c_{r−1} s(n + r − 1) + · · · + "
                + "c_1 s(n + 1) + c_0 s(n). for any sufficiently large n, where the coefficients "
                + "(c_{r−1}, . . . , c_0) are all constants and c_0 ≠ 0.” "
                + "Existence of an order r expresses this property through HasRecurrence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rank", "The least recurrence order", "rank", RankFormula(),
                "Section 2, page 3: “Every constant-recursive sequence satisfies infinitely many "
                + "recurrences, but there is only one of minimal size, that we define to be the "
                + "rank of s(n), and denote it by rank s.” The natural infimum gives that least "
                + "order whenever a recurrence exists; its value on an empty set of orders is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rank-sequence", "Ranks of positive powers", "rankSequence", RankSequenceFormula(),
                "Section 1, page 2: “We say that a sequence of integers is a rank sequence if it "
                + "arises as (rank s(n)^M)_{M≥1} for some constant-recursive integer sequence "
                + "s(n)_{n≥0}.” The exponent M ranges over positive naturals. Equality means "
                + "agreement at every positive exponent, including finite initial segments.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The fixed-rank finiteness conjecture", "claim",
                Disp(Iff(F.Id("claim"), ClaimBody())),
                "Section 1, page 2: “For each r ≥ 1, we conjecture that there are only finitely "
                + "many rank sequences associated with sequences s(n)_{n≥0} of rank r, and we "
                + "are interested in enumerating them.” The set contains exactly the functions "
                + "R : ℕ+ → ℕ equal to rankSequence s for a constant-recursive integer sequence "
                + "s of rank r; r ranges over all positive natural numbers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The finiteness conjecture is false", "result",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "For each natural p ≥ 3, s_p(n) = p·8^n − 4^n − 2^n has rank three. The rank "
                + "of its M-th power is the number of nonzero coefficients of (1 + X − pX²)^M. "
                + "For fixed M, each coefficient in degrees zero through 2M is a nonzero "
                + "polynomial in p: at p = −1 all those coefficients are positive. Thus only "
                + "finitely many natural parameters cause any cancellation at that exponent. "
                + "For every p, the coefficient of X² vanishes at M = 2p + 1. If two parameters "
                + "give the same rank sequence, the second must therefore belong to a finite "
                + "exceptional set determined by the first. Finite fibres and infinitely many "
                + "parameters contradict finiteness at initial rank three. This argument does "
                + "not determine the first cancellation or settle the questions about general "
                + "rank sequences and eventual pseudo-polynomial behaviour.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("rsb-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula RecurrenceFormula()
    {
        var s = F.Id("s");
        var r = F.Id("r");
        var e = F.Id("E");
        var n = F.Id("n");
        var threshold = F.Id("N");
        var h = F.Id("h");
        var order = Member(e, "order");
        var coefficients = All("h", Less(D(0), order),
            NotEqual(Apply(Member(e, "coeffs"), Seq(Langle, D(0), Comma, h, Rangle)), D(0)));
        var tail = LambdaOf("n", Naturals(), RationalCast(Apply(s, Add(n, threshold))));
        var body = Some("E", Call("LinearRecurrence", Rationals()),
            And(Equal(order, r), coefficients,
                Some("N", Naturals(), Apply(Member(e, "IsSolution"), tail))));
        return Disp(All("s", SequenceType(), All("r", Naturals(),
            Iff(Call("HasRecurrence", s, r), body))));
    }

    private static Formula ConstantRecursiveFormula() =>
        Disp(All("s", SequenceType(), Iff(Call("IsConstantRecursive", F.Id("s")),
            Some("r", Naturals(), Call("HasRecurrence", F.Id("s"), F.Id("r"))))));

    private static Formula RankFormula()
    {
        var s = F.Id("s");
        var orders = SetOf("r", Naturals(), Call("HasRecurrence", s, F.Id("r")));
        return Disp(All("s", SequenceType(), Equal(Call("rank", s), Call("sInf", orders))));
    }

    private static Formula RankSequenceFormula()
    {
        var s = F.Id("s");
        var m = F.Id("M");
        var n = F.Id("n");
        var power = LambdaOf("n", Naturals(), new Formula.Power(Apply(s, n),
            Parenthesized(Seq(m, Colon, Sp, Naturals()))));
        return Disp(All("s", SequenceType(), Equal(Call("rankSequence", s),
            LambdaOf("M", PositiveNaturals(), Call("rank", power)))));
    }

    private static Formula ClaimBody()
    {
        var r = F.Id("r");
        var s = F.Id("s");
        var ranks = SetOf("R", RankSequenceType(), Some("s", SequenceType(),
            And(Call("IsConstantRecursive", s), Equal(Call("rank", s), r),
                Equal(F.Id("R"), Call("rankSequence", s)))));
        return All("r", Naturals(), Imply(AtMost(D(1), r),
            Apply(Qualified("Set", "Finite"), ranks)));
    }

    private static Formula SequenceType() => Seq(Naturals(), Sp, To, Sp, Integers());
    private static Formula RankSequenceType() => Seq(PositiveNaturals(), Sp, To, Sp, Naturals());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PositiveNaturals() => new Formula.Power(Naturals(), Plus);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula RationalCast(Formula f) => Parenthesized(Seq(f, Colon, Sp, Rationals()));
    private static Formula Member(Formula value, string name) =>
        Seq(value, Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, domain)), Comma, Sp, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, domain)), Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula domain, Formula body) =>
        Seq(Operatorname, Grp(F.Id("fun")), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, domain)),
            Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula domain, Formula condition) =>
        Seq(OpenBrace, F.Id(name), Colon, Sp, domain, Sp, Mid, Sp, Parenthesized(condition), CloseBrace);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imply(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b, Formula c) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And,
            new Formula.Logic(Parenthesized(b), FormulaLogicOperator.And, Parenthesized(c)));
}
