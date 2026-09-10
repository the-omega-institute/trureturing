using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.SubsetSums;

internal sealed class ModSixResidueCountsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/oeis2025a068012");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete residue table proves Corneth's second recurrence for OEIS A068012.",
        H("The Residue Table and Corneth's Correction Recurrence"),
        Blocks(
            Paragraph(Text(
                "C and a are the definitions from the frozen module "
                + "D5/S1/Recurrence/Parity/SubsetSumModSixDoubling: C(m,r) counts subsets "
                + "of the interval from one to m with sum r in ZMod 6, and a(m)=C(m,0). "
                + "That module already proves the doubling recurrence. Here the full "
                + "residue table proves the second recurrence in Corneth's "
                + "September 13, 2025 FORMULA contribution to OEIS A068012.")),
            Paragraph(Text(
                "Indices m and k, counts, and powers are natural numbers. The residue r "
                + "lies in ZMod 6; constants compared with r belong to that ring. "
                + "The operator div is integer division, mod is remainder, and "
                + "subtraction in an exponent is truncated natural subtraction. "
                + "The conditional expressions below have propositions as branches.")),
            Node("count_closed_form", "The complete residue table", ClosedFormula(),
                "At m=3 the six counts are 2,1,1,2,1,1. Natural-number induction "
                + "propagates the table using the frozen count_succ recurrence. "
                + "The quotient m div 3 increases exactly when m mod 3 is two, "
                + "doubling the correction power. Splitting m modulo six and the "
                + "six residues evaluates the shift in ZMod 6 and closes every "
                + "inductive branch. The interval size has no upper bound.",
                AssessedProvenance.FromRepo()),
            Node("corneth_step", "Corneth's second recurrence", StepFormula(),
                "Apply the table at residue zero for 3k and 3k+1, then use "
                + "2^k=2*2^(k-1). Multiplying the desired identity by six makes "
                + "the two table equations cancel. The correction is moved left, "
                + "so the equality also establishes the nonnegativity required "
                + "by the source's subtraction form.",
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a068012-correction-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("mod-six-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S1/Recurrence/SubsetSums/ModSixResidueCounts." + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, claim);

    private static Formula ClosedFormula()
    {
        Formula size = F.Id("m");
        Formula correction = Power(D(2), Call("div", size, D(3)));
        Formula total = Power(D(2), size);
        Formula scaled = Mul(D(6), Call("C", size, R()));
        Formula table = Conditional(Equal(Mod(size, D(3)), D(1)),
            Conditional(Seq(Equal(R(), D(2)), Sp, Lor, Sp, Equal(R(), D(5))),
                Equal(Add(scaled, Mul(D(2), correction)), total),
                Equal(scaled, Add(total, correction))),
            Conditional(Seq(Equal(R(), D(0)), Sp, Lor, Sp, Equal(R(), D(3))),
                Equal(scaled, Add(total, Mul(D(2), correction))),
                Equal(Add(scaled, correction), total)));
        return Disp(Seq(Bound("m"), Sp, D(3), Sp, Le, Sp, size, Sp, Implies, Sp,
            Forall, Sp, R(), Sp, InMacro, Sp, Call("ZMod", D(6)), Comma, Sp, table));
    }

    private static Formula StepFormula()
    {
        Formula index = F.Id("k");
        Formula triple = Mul(D(3), index);
        return Disp(Seq(Bound("k"), Sp, D(1), Sp, Le, Sp, index, Sp, Implies, Sp,
            Equal(Add(Call("a", Add(triple, D(1))),
                Power(D(2), Subtract(index, D(1)))), Mul(D(2), Call("a", triple)))));
    }

    private static Formula R() => F.Id("r");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Mod(Formula value, Formula modulus) => new Formula.Modulo(value, modulus);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp,
        Parenthesized(yes), Sp, Named("else"), Sp, Parenthesized(no));
    private static Formula Bound(string name) => Seq(
        Forall, Sp, F.Id(name), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma);
}
