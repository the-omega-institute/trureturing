using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class DigitSumSquareLeastWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/wu2025a389000");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu's conjecture for the least simultaneous digit-sum witness in OEIS A389000.",
        H("The Least Simultaneous Digit-Sum Witness"),
        Blocks(
            Paragraph(Text(
                "The sequence definition and the conjecture are those of OEIS A389000 "
                + "(Chai Wah Wu, October 1, 2025), recorded in the literature note "
                + "wu2025a389000. The OEIS rendering 210^(2*m+1)-1 means 2 times 10^(2*m+1), minus 1.")),
            Paragraph(Text(
                "All variables and operations are over the natural numbers. The notation digits(10,x) "
                + "means Nat.digits 10 x, and sum means List.sum. Subtraction is "
                + "natural subtraction. The natural infimum selects the least member of a "
                + "nonempty set and is zero for an empty set.")),
            Node("digitSum", "Base-ten digit sum", DigitSumFormula(),
                "This definition binds Mathlib's base-ten digits and list sum.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a", "The least positive witness", SequenceFormula(),
                "The defining set requires positivity and both divisibility conditions. "
                + "The two digit-sum identities below make it nonempty at every index 9m+5.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("digitSum_witness", "The candidate's digit sum", WitnessFormula(false),
                "Induction on the number of trailing nines gives digitSum(c times 10^d minus 1) "
                + "equal to 9d+c-1 for 1 <= c <= 10. Taking c=2 and d=2m+1 gives the identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("digitSum_witness_sq", "The square's digit sum", WitnessFormula(true),
                "With d=2m, the square is 10 times (10^d times (10 times (4 times 10^d minus 1) "
                + "plus 6)) plus 1. Digit recursion removes the final 1 and the zero block, "
                + "then the final 6. The remaining digit sum is 9d+3, giving 9d+10 overall.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("wu_conjecture", "Wu's conjecture", ConjectureFormula(),
                "Put n=9m+5, L=2m+1, and K=2 times 10^L minus 1. An inductive leading-digit "
                + "ceiling and its equality case show that 0<k<K implies digitSum(k)<2n. "
                + "If n divides this positive sum, it equals n. Mathlib's mod-nine digit-sum "
                + "congruence then gives k mod 9 = 5 and digitSum(k^2) mod 9 = 7. Writing "
                + "digitSum(k^2)=nt yields 5t mod 9 = 7, so t>=5. But k^2<4 times 10^(2L) "
                + "gives digitSum(k^2)<=18L+3=36m+21<5n, a contradiction. The candidate "
                + "satisfies both divisibility conditions, hence is the least element.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a389000-digit-sum-square-least-witness"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a389000-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DigitSumFormula()
    {
        var x = F.Id("x");
        return Universal(x, Equal(Call("digitSum", x), Call("sum", Call("digits", D(1, 0), x))));
    }

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var conditions = Seq(D(0), Sp, Lt, Sp, k, Sp, Land, Sp,
            Parenthesized(Seq(Divides(n, Call("digitSum", k)), Sp, Land, Sp,
                Divides(n, Call("digitSum", Power(k, D(2)))))));
        var witnesses = Seq(OpenBrace, k, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            conditions, CloseBrace);
        return Universal(n, Equal(Call("a", n), Call("sInf", witnesses)));
    }

    private static Formula WitnessFormula(bool square)
    {
        var m = F.Id("m");
        var candidate = Candidate(m);
        return Universal(m, Equal(Call("digitSum", square ? Power(Parenthesized(candidate), D(2)) : candidate),
            Multiply(D(2), Parenthesized(Index(m)))));
    }

    private static Formula ConjectureFormula()
    {
        var m = F.Id("m");
        return Universal(m, Equal(Call("a", Index(m)), Candidate(m)));
    }

    private static Formula Index(Formula m) => Add(Multiply(D(9), m), D(5));
    private static Formula Candidate(Formula m) => Subtract(
        Multiply(D(2), Power(D(1, 0), Add(Multiply(D(2), m), D(1)))), D(1));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Universal(Formula variable, Formula body) => Disp(Seq(
        Forall, Sp, variable, Sp, InMacro, Sp, Naturals(), Comma, Sp, body));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.Add(Comma);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
