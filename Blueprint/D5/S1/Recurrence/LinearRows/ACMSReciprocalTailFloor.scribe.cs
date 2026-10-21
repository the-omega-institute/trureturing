using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.LinearRows;

internal sealed class ACMSReciprocalTailFloorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/amdeberhanchenmollsagan2014fibonomial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generalized Fibonacci reciprocal tails have the conjectured integer floor.",
        H("Reciprocal Tails of Generalized Fibonacci Numbers"),
        Blocks(
            Paragraph(Text("Amdeberhan, Chen, Moll and Sagan's Conjecture 4.6 has two clauses. "
                + "The theorem here proves its first clause, including convergence of the tail. "
                + "The clause concerning squared reciprocals is not asserted here.")),
            Describe.Lean(DescribeId.Create("acms-tail-sequence"),
                DeclarationHandle.Create(Prefix + "U"), H("The generalized Fibonacci sequence"),
                StatementSource.FromAuthor(Disp(SequenceBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Section 1, p. 2: \"Throughout this work, P will stand for the "
                    + "positive integers.\" \"{0}_{s,t} = 0, {1}_{s,t} = 1 and, for n ≥ 2, "
                    + "{n}_{s,t} = s{n − 1}_{s,t} + t{n − 2}_{s,t}.\" "
                    + "U uses integer coefficients s and t and natural indices. The three equations "
                    + "display all cases of its recursive definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("acms-tail-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Conjecture 4.6, first clause"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("claim"), Sp, Iff, Sp,
                    Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 4.6, p. 13: \"If s > t ≥ 1 with "
                    + "(s, −t) ≠ (2, −1) and n, r ∈ P then "
                    + "⌊(∑_{k=n}^∞ 1/{rk}_{s,−t})^{−1}⌋ = "
                    + "{rn}_{s,−t} − {r(n − 1)}_{s,−t} − 1.\" "
                    + "The index k in the displayed infinite sum starts at zero, so the source "
                    + "index is n+k. Summable records convergence explicitly. Each denominator "
                    + "is cast from the integer U value to the reals; the floor and right side "
                    + "are integers. Nat.sub is subtraction in the natural indices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("acms-tail-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The reciprocal-tail floor identity"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The companion matrix of U at stride r yields a real "
                    + "recurrence a(k+2)=P a(k+1)−Q a(k), with Q=t^r and a(1)=c=U(s,−t,r). "
                    + "Its parameters satisfy Q≥1, P≥Q+1, P≥3 and P≥c+1. Induction bounds "
                    + "the successive difference fwdDiff(1,a,k) below by c(k+1). Cassini's "
                    + "identity gives a(k+1)^2−a(k)a(k+2)=c^2 Q^k, and a second induction "
                    + "bounds this defect plus one by a(k+2)−a(k). Dividing by positive "
                    + "denominators places each reciprocal between two telescoping differences. "
                    + "Their sums put the reciprocal tail in the interval whose integer floor "
                    + "is the stated difference minus one. The endpoint with difference one "
                    + "uses positivity and the strict lower tail estimate."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("amdeberhan-chen-moll-sagan-2014-reciprocal-tail-floor-conjecture-4-6"),
                    ResolutionKind.Proved)))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Imp(Formula hypothesis, Formula body) =>
        Seq(Parenthesized(hypothesis), Sp, Implies, Sp, Parenthesized(body));
    private static Formula LeF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula U(Formula s, Formula t, Formula k) => Call("U", s, t, k);

    private static Formula SequenceBody()
    {
        var s = F.Id("s");
        var t = F.Id("t");
        var n = F.Id("n");
        return All("s", Z(), All("t", Z(), And(Equal(U(s, t, D(0)), D(0)),
            And(Equal(U(s, t, D(1)), D(1)), All("n", N(),
                Equal(U(s, t, Add(n, D(2))),
                    Add(Multiply(s, U(s, t, Add(n, D(1)))), Multiply(t, U(s, t, n)))))))));
    }

    private static Formula ClaimBody()
    {
        var s = F.Id("s");
        var t = F.Id("t");
        var n = F.Id("n");
        var r = F.Id("r");
        var k = F.Id("k");
        var nt = new Formula.Negate(t);
        var denominator = Parenthesized(Seq(U(s, nt, Multiply(r, Parenthesized(Add(n, k)))),
            Colon, Sp, R()));
        var term = new Formula.Fraction(Seq(Parenthesized(Seq(D(1), Colon, Sp, R()))), denominator);
        var function = Parenthesized(Seq(k, Colon, Sp, N(), Sp, Mapsto, Sp, term));
        var sum = Seq(Sum, Apos, Underscore, Grp(k, Colon, Sp, N()), Sp, term);
        var previous = new Formula.Apply(Qualified("Nat", "sub"), [n, D(1)]);
        var endpoint = Subtract(Subtract(U(s, nt, Multiply(r, n)),
            U(s, nt, Multiply(r, Parenthesized(previous)))), D(1));
        var conclusion = And(Call("Summable", function),
            Equal(new Formula.Floor(new Formula.Power(Parenthesized(sum),
                new Formula.Negate(D(1)))), endpoint));
        var excluded = NotEqual(Parenthesized(Seq(s, Comma, Sp, nt)),
            Parenthesized(Seq(D(2), Comma, Sp, new Formula.Negate(D(1)))));
        return All("s", Z(), All("t", Z(), Imp(LeF(D(1), t),
            Imp(new Formula.Relation(t, FormulaRelationOperator.LessThan, s), Imp(excluded,
                All("n", N(), All("r", N(), Imp(LeF(D(1), n), Imp(LeF(D(1), r), conclusion)))))))));
    }
}
