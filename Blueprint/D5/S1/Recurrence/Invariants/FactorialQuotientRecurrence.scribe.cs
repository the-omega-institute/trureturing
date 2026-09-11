using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class FactorialQuotientRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/kimberling2024a372991");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The factorial-quotient sequence satisfies Mathar's linear recurrence and is integral.",
        H("The Factorial-Quotient Recurrence of OEIS A372991"),
        Blocks(
            Paragraph(Text("All indices are natural numbers and a takes values in the rationals. "
                + "Factorials and natural witnesses k are cast to the rationals in equalities. "
                + "The quotient defining a is rational division. In the coefficient 2n(2n-1), "
                + "n is cast to the rationals before arithmetic; subtraction in the index n-3 "
                + "is natural subtraction. The hypothesis n >= 3 makes this the displayed "
                + "formula of Mathar's conjecture.")),
            Node("a", "The factorial-quotient sequence", DefinitionFormula(),
                "The rational definition follows the name of OEIS A372991 with initial "
                + "values a(0)=a(1)=1. Integrality is proved below, rather than assumed "
                + "when forming the quotient.", DescribeRole.Definition,
                AssessedProvenance.FromRepo()),
            Node("a_pos", "Every term is positive",
                Universal(Seq(D(0), Sp, Lt, Sp, A(N()))),
                "Two-step induction combines positivity of the factorial with positivity "
                + "of the two preceding terms. Thus every factor later cancelled is nonzero.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("triple_product", "The consecutive triple product",
                Universal(Equal(Mul(Mul(A(Add(N(), D(2))), A(Add(N(), D(1)))), A(N())),
                    Factorial(Mul(D(2), Parenthesized(Add(N(), D(2))))))),
                "Multiply the defining rational quotient by its nonzero denominator. "
                + "The positivity theorem justifies this cancellation at every index.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("mathar_recurrence", "Mathar's conjectured linear recurrence",
                Universal(Seq(D(3), Sp, Le, Sp, N(), Sp, Implies, Sp,
                    Equal(A(N()), Mul(Mul(Mul(D(2), N()),
                        Parenthesized(Subtract(Mul(D(2), N()), D(1)))),
                        A(Subtract(N(), D(3))))))),
                "Consecutive triple products share two positive factors. Cancelling "
                + "those factors telescopes the quotient to (2n)!/(2n-2)!. Two applications "
                + "of the factorial successor identity give the coefficient 2n(2n-1). "
                + "This proves the conjecture for every n at least three.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a372991-factorial-quotient-linear-recurrence"),
                    ResolutionKind.Proved)),
            Node("a_integral", "Every term is a natural number",
                Universal(Seq(Exists, Sp, F.Id("k"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
                    Equal(A(N()), F.Id("k")))),
                "Strong induction uses the linear recurrence and the natural witness "
                + "2n(2n-1)k obtained from the witness k at n-3. The three base cases "
                + "are discharged inside the induction proof. This is an unbounded "
                + "integrality theorem, not a finite table of sequence values.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("factorial-quotient-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DefinitionFormula() => Disp(new Formula.Aligned([
        Seq(F.Id("a"), Colon, Sp, Naturals(), Sp, To, Sp, Mathbb, Grp(F.Id("Q"))),
        Equal(A(D(0)), D(1)),
        Equal(A(D(1)), D(1)),
        Seq(Bound(), Sp, Equal(A(Add(N(), D(2))),
            new Formula.Fraction(Factorial(Mul(D(2), Parenthesized(Add(N(), D(2))))),
                Mul(A(Add(N(), D(1))), A(N())))))
    ]));

    private static Formula N() => F.Id("n");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bound() => Seq(Forall, Sp, N(), Sp, InMacro, Sp, Naturals(), Comma);
    private static Formula Universal(Formula body) => Disp(Seq(Bound(), Sp, body));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula A(Formula index) => new Formula.Apply(F.Id("a"), [index]);
    private static Formula Factorial(Formula value) => Seq(Parenthesized(value), Bang);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
