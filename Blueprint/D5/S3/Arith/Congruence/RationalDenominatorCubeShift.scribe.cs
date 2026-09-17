using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class RationalDenominatorCubeShiftDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/RationalDenominatorCubeShift.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cicuttin2017a152020");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A residue-class gcd identity proves Cicuttin's denominator formula for OEIS A152020.",
        H("The Rational-Denominator Cube Shift"),
        Blocks(
            Node("a", "The A152020 denominator sequence", SequenceFormula(),
                "For n >= 1, the reduced denominator Rat.den of 8/(9*n^2) is divisible by 9, "
                + "so the natural-number division by 9 defining a(n) is exact. At n = 0, "
                + "8/(9*0^2) is 0 in the rationals with denominator 1, and a(0) = 0 is the "
                + "junk value of the totalized definition. The theorem quantifies over n >= 1 only.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cicuttin_a152020", "Cicuttin's denominator formula", TheoremFormula(),
                "For a positive index n, the numerator n minus 2 is formed in the integers, "
                + "then cubed and divided by n squared in the rationals. Reduced-denominator "
                + "formulas turn both sides into gcd quotients. Splitting n modulo 4 proves "
                + "that gcd(n squared,(n-2) cubed) equals gcd(n squared,8): the common value "
                + "is 1 for odd n, 4 when n is 2 modulo 4, and 8 when 4 divides n. The index "
                + "n=1 is evaluated separately.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a152020-rational-denominator-cube-shift"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a152020-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var input = Fraction(D(8), Multiply(D(9), Power(n, D(2))));
        return Disp(Universal(n, Equal(Call("a", n), Fraction(Call("den", input), D(9)))));
    }

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        var shiftedCube = Power(Parenthesized(Subtract(n, D(2))), D(3));
        var quotient = Fraction(shiftedCube, Power(n, D(2)));
        return Disp(Universal(n, Seq(
            D(1), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            Equal(Call("a", n), Call("den", quotient)))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Universal(Formula variable, Formula body) => Seq(
        Forall, Sp, variable, Sp, InMacro, Sp, Naturals(), Comma, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
