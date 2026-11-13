using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MatharA116387SixTermRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MatharA116387SixTermRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2011a116387");
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Series => Call("PowerSeries", Q);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula f, int k) => new Formula.Power(f,
        k < 0 ? new Formula.Negate(Num(-k)) : Num(k));
    private static Formula Product(params Formula[] fs) => fs.Aggregate(Multiply);
    private static Formula SumOf(params Formula[] fs) => fs.Aggregate(Add);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula MotzkinLaw(Formula m) => Equal(m,
        SumOf(Num(1), Product(F.Id("X"), m), Product(Pow(F.Id("X"), 2), Pow(m, 2))));
    private static Formula Radicand => Subtract(Subtract(Num(1), Product(Num(2), F.Id("X"))),
        Product(Num(3), Pow(F.Id("X"), 2)));
    private static Formula NativeSpec() => And(
        And(Equal(Call("constantCoeff", F.Id("M")), Num(1)), MotzkinLaw(F.Id("M"))),
        And(All("m", Series, Implies(MotzkinLaw(F.Id("m")), Equal(F.Id("m"), F.Id("M")))),
        And(And(Equal(Call("constantCoeff", F.Id("y")), Num(1)), Equal(Pow(F.Id("y"), 2), Radicand)),
        And(All("z", Series, Implies(Equal(Call("constantCoeff", F.Id("z")), Num(1)),
                Implies(Equal(Pow(F.Id("z"), 2), Radicand), Equal(F.Id("z"), F.Id("y"))))),
            Equal(Product(F.Id("y"), Par(Subtract(Num(2), F.Id("M"))), F.Id("F")), Num(1))))));

    private static Formula Recurrence()
    {
        Formula n = F.Id("n");
        Formula r = Par(Seq(n, Colon, Q));
        Formula An(int k) => Call("a", k == 0 ? n : Subtract(n, Num(k)));
        Formula equation = Equal(SumOf(
            Product(r, Par(Subtract(Product(Num(17), r), Num(142))), An(0)),
            Product(Par(SumOf(Product(Num(17), Pow(r, 2)), Product(Num(95), r), Num(138))), An(1)),
            Product(Par(Subtract(Add(Product(new Formula.Negate(Num(391)), Pow(r, 2)), Product(Num(2488), r)), Num(2908))), An(2)),
            Product(Par(Add(Subtract(Product(new Formula.Negate(Num(17)), Pow(r, 2)), Product(Num(603), r)), Num(1892))), An(3)),
            Product(Num(2), Par(Subtract(Product(Num(697), r), Num(2021))), Par(Subtract(r, Num(4))), An(4)),
            Product(Num(60), Par(Subtract(Product(Num(17), r), Num(47))), Par(Subtract(r, Num(4))), An(5))), Num(0));
        return All("n", Nat, Implies(
            new Formula.Relation(Num(5), FormulaRelationOperator.LessThanOrEqual, n), equation));
    }

    private static DocumentBlock Node(string name, string title, Formula body,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a116387-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(body)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-term recurrence for the native Motzkin transform A116387.",
        H("The A116387 Motzkin transform"),
        Blocks(
            Paragraph(Text("Work in ordinary formal power series over Q. The symbol c denotes Mathlib's "
                + "natural Catalan generating function mapped coefficientwise to Q. Its application to a "
                + "series with zero constant coefficient means formal substitution. All coefficient indices "
                + "are natural numbers; recurrence scalars are evaluated in Q. The square root always has "
                + "constant coefficient one.")),
            Node("M", "The native Motzkin generating function",
                Equal(F.Id("M"), Product(Pow(Par(Subtract(Num(1), F.Id("X"))), -1),
                    Call("c", Product(Pow(F.Id("X"), 2), Pow(Par(Subtract(Num(1), F.Id("X"))), -2))))),
                AssessedProvenance.FromLiterature(Source),
                "This is the native A001006 formula c(X²/(1-X)²)/(1-X). The inverse exists because "
                + "1-X has constant coefficient one, and the substituted series has constant coefficient zero. "
                + "The Catalan quadratic gives M=1+XM+X²M² and M(0)=1. If m is another solution, "
                + "(1-X-X²(m+M))(m-M)=0. The first factor has constant coefficient one, so m=M.",
                DescribeRole.Definition),
            Node("y", "The normalized root",
                Equal(F.Id("y"), Subtract(Subtract(Num(1), F.Id("X")), Product(Num(2), Pow(F.Id("X"), 2), F.Id("M")))),
                AssessedProvenance.FromRepo(Source),
                "The Motzkin quadratic implies y²=1-2X-3X² and y(0)=1. If z has the same square "
                + "and constant coefficient, (z+y)(z-y)=0; z+y has constant coefficient two. Thus z=y. "
                + "The identity 2X²M=1-X-y uses no inverse of X.", DescribeRole.Definition),
            Node("F", "The exact source transform",
                Equal(F.Id("F"), Pow(Par(Product(F.Id("y"), Par(Subtract(Num(2), F.Id("M"))))), -1)),
                AssessedProvenance.FromLiterature(Source),
                "OEIS A116387 defines this generating function. Its denominator has constant coefficient "
                + "one, so the inverse is an actual unit inverse in Q[[X]].", DescribeRole.Definition),
            Node("a", "The offset-zero coefficients",
                All("n", Nat, Equal(Call("a", F.Id("n")), Call("coeff", F.Id("n"), F.Id("F")))),
                AssessedProvenance.FromLiterature(Source),
                "The first coefficient has index zero. Every lagged index below is nonnegative on n≥5.",
                DescribeRole.Definition),
            Node("native_spec", "The native source characterization",
                new Formula.Logic(F.Id("S"), FormulaLogicOperator.Iff, NativeSpec()),
                AssessedProvenance.FromRepo(Source),
                "The proposition S includes the constructed Motzkin solution, its uniqueness, "
                + "the normalized root and its uniqueness, and the inverse equation for F.", DescribeRole.Definition),
            Node("claim", "The complete six-term assertion",
                new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, And(NativeSpec(), Recurrence())),
                AssessedProvenance.FromLiterature(Source),
                "Mathar's printed conjecture gives these six polynomial coefficients in this order. "
                + "It prints no onset. The range n≥5 is the full well-formed offset-zero interpretation; "
                + "OFFSET 0,2 does not specify a recurrence onset. The source characterization makes "
                + "existence and branch normalization explicit.", DescribeRole.Definition),
            Node("result", "The native six-term recurrence", And(NativeSpec(), Recurrence()),
                AssessedProvenance.FromRepo(Source),
                "Put p=1-X-4X², q=1-2X-4X² and d=1-2X-3X². The native quadratic and inverse "
                + "equation give 2qyF=y+p. Differentiate this identity and y²=d to obtain DF'-eF=f, "
                + "where D=pqd, e=2-2X-14X²-14X³+40X⁴+48X⁵ and f=2X-6X²-6X³. "
                + "For theta=X d/dX let L be the ordered sum of X^j P_j(theta+j), j=0,...,5, "
                + "with P_j the six displayed polynomials. Multiplying the differentiated equation by "
                + "w=17X²(5X+1) and the original equation by v=-5X(47X+25) gives "
                + "pLF=wf'+vf=6pX²(5X-36). Cancel p, whose constant coefficient is one. "
                + "The forcing has degree three. The Euler coefficient identity and all six shifts "
                + "therefore give the printed recurrence for every n≥5, including n=5.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("oeis-a116387-six-term-recurrence"), ResolutionKind.Proved)))));
}
