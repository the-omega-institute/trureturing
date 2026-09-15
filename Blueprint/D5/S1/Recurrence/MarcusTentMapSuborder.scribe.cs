using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MarcusTentMapSuborderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MarcusTentMapSuborder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marcus's tent-map cycle length equals the signed suborder of two.",
        H("Marcus's Tent-Map Cycle Length"),
        Blocks(
            Paragraph(Text(
                "The tent map on [0,1] sends x to 1-|2x-1|. The symbols n, N, k, "
                    + "and m denote natural numbers; N=2n+1 in the theorem. For N>0 "
                    + "and k<=N, tent(N,k) is its numerator action at the rational "
                    + "point k/N. Subtraction is natural subtraction, with no "
                    + "truncation in either orbit branch. The function minimalPeriod "
                    + "gives the least positive return time of a point, or zero "
                    + "when there is no positive return. The signed suborder of 2 "
                    + "modulo 2n+1 is the least m>0 with 2^m congruent to 1 or -1; "
                    + "the latter residue is written 2n. Congruence means that the "
                    + "modulus divides the integer difference, and IsLeast asserts membership "
                    + "in the displayed set and a lower bound for every member. "
                    + "Only Marcus's Jul 16 2025 cycle-length sentence in A003558 is "
                    + "settled here. Kaprekar cycles, x^2-2 iteration, and the "
                    + "Kappraff-Adamson base conjecture are not claimed. The hypothesis "
                    + "n>0 excludes n=0, where N=1 and 2/N is outside [0,1].")),
            Describe.Lean(
                DescribeId.Create("a003558-tent"),
                DeclarationHandle.Create(Prefix + "tent"),
                H("The numerator tent map"),
                StatementSource.FromAuthor(TentFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/marcus2025a003558")),
                Blocks(Paragraph(Text(
                    "If 2k<=N, the absolute-value expression equals 2k/N. If N<2k "
                        + "and k<=N, it equals (2N-2k)/N, and the nonnegative "
                        + "numerator agrees with natural subtraction. The displayed "
                        + "definition is total on natural N and k; its interpretation "
                        + "as a rational tent-map numerator uses N>0 and k<=N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a003558-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The cycle-length conjecture"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/marcus2025a003558")),
                Blocks(Paragraph(Text(
                    "For N=2n+1, induction shows that every iterate from numerator 2 "
                        + "stays even and at most N, and represents either sign of "
                        + "2^(m+1) modulo N. Since N is odd, the even representative "
                        + "of either sign of 2 in this interval must be 2. Cancelling "
                        + "the unit 2 therefore makes a return at time m equivalent "
                        + "to 2^m being congruent to 1 or -1. Euler's theorem supplies "
                        + "a positive return, and minimalPeriod gives the least one. "
                        + "Division by the fixed positive N preserves equality of "
                        + "numerators, so these are also the return times of 2/N."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a003558-marcus-tent-map-suborder"),
                    ResolutionKind.Proved)))));

    private static Formula TentFormula()
    {
        var modulus = F.Id("N");
        var k = F.Id("k");
        var twiceK = Multiply(D(2), k);
        var cases = Seq(
            Begin, Grp(F.Id("cases")),
            twiceK, Amp, Sp,
            Parenthesized(new Formula.Relation(
                twiceK, FormulaRelationOperator.LessThanOrEqual, modulus)),
            RowBreak,
            Subtract(Multiply(D(2), modulus), twiceK), Amp, Sp,
            Parenthesized(new Formula.Relation(
                modulus, FormulaRelationOperator.LessThan, twiceK)),
            End, Grp(F.Id("cases")));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("N"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("k"), Naturals()),
            ],
            new Formula.Relation(Call("tent", modulus, k),
                FormulaRelationOperator.Equal, cases)));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var twiceN = Multiply(D(2), n);
        var modulus = Add(twiceN, D(1));
        var power = new Formula.Power(D(2), m);
        var signedPower = new Formula.Logic(
            Parenthesized(Congruent(power, D(1), modulus)),
            FormulaLogicOperator.Or,
            Parenthesized(Congruent(power, twiceN, modulus)));
        var condition = new Formula.Logic(
            Parenthesized(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, m)),
            FormulaLogicOperator.And, Parenthesized(signedPower));
        var periods = Seq(
            Left, OpenBrace,
            new Formula.Relation(m, FormulaRelationOperator.MemberOf, Naturals()),
            Sp, Mid, Sp, condition, Right, CloseBrace);
        var period = Call("minimalPeriod", Call("tent", modulus), D(2));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals())],
            new Formula.Logic(
                Parenthesized(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n)),
                FormulaLogicOperator.Implies,
                Parenthesized(Call("IsLeast", periods, period)))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(new Formula.Relation(left, FormulaRelationOperator.Equivalent, right), Sp,
            Parenthesized(Seq(Operatorname, Grp(F.Id("mod")), Sp, modulus)));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
