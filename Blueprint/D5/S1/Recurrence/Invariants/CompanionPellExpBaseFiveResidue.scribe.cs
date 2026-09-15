using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CompanionPellExpBaseFiveResidueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2012a204061");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A204061 residues mod 5 are one exactly when no base-5 digit is two.",
        H("Hanna's Companion Pell Exponential Residues"),
        Blocks(
            Paragraph(Text("The symbols N and Z denote the natural numbers and integers; "
                + "Q_5 (ℚ₅) is the field of 5-adic numbers and Z_5 (ℤ₅) its ring of integers, "
                + "with the primality fact Nat.prime_five supplied inline. "
                + "PowerSeries(Q_5) is the formal power-series ring with indeterminate X. "
                + "The operator exp(Q_5) denotes its formal exponential series, "
                + "subst(F,E) substitutes E into F, and coeff(n,F) extracts coefficient n. "
                + "The operator toZMod maps Z_5 to ZMod(5), the integers modulo five; "
                + "digits_5(n) is the list of base-five digits of n, with digits_5(0) empty. "
                + "The indices n and k are natural numbers. The exponent uses the frozen "
                + "companion-Pell sequence Q of D5/S1/Recurrence/PellCompanionGcd "
                + "(A001333, one-half the companion Pell numbers), and a is the exponential "
                + "coefficient function. A type annotation "
                + "in Q_5 indicates the canonical embedding of an integer, natural number, "
                + "or 5-adic integer. The sum is formal, has zero constant coefficient, "
                + "and uses division in Q_5.")),
            Node("a", "The Pell-square exponential coefficients", CoefficientFormula(),
                "The defining exponential of OEIS A204061 is read in Q_5. "
                + "Its exponent uses the frozen companion-Pell sequence Q of "
                + "D5/S1/Recurrence/PellCompanionGcd (A001333, one-half the companion Pell "
                + "numbers). The coefficient formula directly uses that exponential, with a zero "
                + "constant term in its exponent. Integrality over Z is not asserted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The A204061 base-five residue conjecture", ResultFormula(),
                "The squared Pell recurrence and formal differentiation give f(0)=1 "
                + "and f^4(1+X)^2(1-6X+X^2)=1 for the exponential series f. "
                + "A binomial series over Z_5 constructs an integral fourth root, "
                + "which agrees with f by uniqueness at constant coefficient one. "
                + "After reduction modulo five, Frobenius yields "
                + "B=(1+X+X^3+X^4)B(X^5). Coefficient extraction and induction "
                + "on n through n/5 give zero exactly when a digit two occurs, "
                + "and one otherwise. The displayed residue law is Hanna's conjecture "
                + "in this 5-adic reading.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a204061-companion-pell-exp-base-five-residue"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a204061-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula QFive() => new Formula.Subscript(Seq(Mathbb, Grp(F.Id("Q"))), D(5));
    private static Formula ZFive() => new Formula.Subscript(Integers(), D(5));
    private static Formula Series() => Call("PowerSeries", QFive());
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula InQFive(Formula value) => Parenthesized(Seq(value, Colon, Sp, QFive()));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula summand = new Formula.Fraction(
            Mul(Power(InQFive(Call("Q", k)), D(2)), Power(F.Id("X"), k)), InQFive(k));
        Formula exponent = Seq(new Formula.Subscript(F.Sum,
            Seq(k, Colon, Sp, Naturals(), Comma, Sp, D(1), Sp, Le, Sp, k)),
            Sp, Parenthesized(summand));
        Formula typedExponent = Parenthesized(Seq(exponent, Colon, Sp, Series()));
        return Disp(Seq(Bound("n", Naturals()), Equal(InQFive(Call("a", n)),
            Call("coeff", n, Call("subst", Call("exp", QFive()), typedExponent)))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula z = F.Id("z");
        Formula digits = new Formula.Apply(new Formula.Subscript(Named("digits"), D(5)), [n]);
        Formula condition = Seq(D(2), Sp, InMacro, Sp, digits);
        Formula residue = Parenthesized(Seq(Named("if"), Sp, Parenthesized(condition), Sp,
            Named("then"), Sp, D(0), Sp, Named("else"), Sp, D(1)));
        return Disp(Seq(Bound("n", Naturals()), Exists, Sp, z, Colon, Sp, ZFive(), Comma, Sp,
            Conjunction(Equal(InQFive(z), Call("a", n)),
                Equal(Call("toZMod", z), residue))));
    }
}
