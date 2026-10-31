using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA027182SelfConvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA027182SelfConvolution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/matharkimberling2026a027182");
    private const string ArrayQuote =
        "OEIS A027170, revision 32, definition (unpaginated): \"Triangular array T read by rows (4-diamondization of Pascal's triangle). Step 1: t(n,k) = C(n+2,k+1) + C(n+1,k) + C(n+1,k+1) + C(n,k). Step 2: T(n,k) = t(n,k) - t(0,0) + 1. Domain: 0 <= k <= n, n >= 0.\" ";
    private const string SequenceQuote =
        "OEIS A027182, revision 8, name and comment (unpaginated): \"a(n) = self-convolution of row n of array T given by A027170.\" "
        + "\"Let g(x) = Sum_(k=0..n) A027170(n,k)*x^k be the generating function of row n, then a(n) = [x^n] g(x)^2. - R. J. Mathar, May 06 2026\" ";
    private const string ClaimQuote =
        "OEIS A027182, revision 8, FORMULA field (unpaginated): \"Conjecture: D-finite with recurrence 2*(n+2)*a(n) +(-17*n-23)*a(n-1) +(47*n+36)*a(n-2) +2*(-22*n-17)*a(n-3) +4*(-n+20)*a(n-4) +8*(2*n-9)*a(n-5) +24*(12*n-47)=0. - R. J. Mathar, May 06 2026\" ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The central self-convolution of the four-diamondized Pascal row satisfies the six-term recurrence in OEIS A027182.",
        H("Mathar and Kimberling's self-convolution recurrence"),
        Blocks(
            Node("t", "The four binomial coefficients", TSmallFormula(), ArrayQuote
                + "The indices n and k are natural numbers, and Nat.choose is the ordinary binomial coefficient.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("T", "The diamondized row", TFormula(), ArrayQuote
                + "The subtraction is natural subtraction; the stated row domain is 0 <= k <= n. The formula defines a total natural-valued function.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("g", "The row polynomial", GFormula(), SequenceQuote
                + "The polynomial has natural coefficients. Finset.range(n+1) includes both row endpoints 0 and n; Polynomial.C and Polynomial.X form each monomial.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The central coefficient of the square", AFormula(), SequenceQuote
                + "Polynomial.coeff extracts the coefficient with natural index n. The source sequence starts at 1; the same expression defines a(0)=1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured recurrence", Disp(new Formula.Logic(F.Id("claim"),
                FormulaLogicOperator.Iff, Parenthesized(ClaimBody()))), ClaimQuote
                + "The proposition ranges over every natural n with 6 <= n. Sequence indices use natural subtraction. Each sequence value and n are cast to the integers before coefficient arithmetic. The proposition asserts the displayed recurrence; no separate D-finiteness predicate is asserted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The recurrence holds", Disp(ClaimBody()),
                "Symmetry of the row turns its central self-convolution into a sum of squares. Vandermonde's identity evaluates the square and mixed binomial sums. "
                + "The resulting closed form is a combination of three consecutive central binomial coefficients, an exponential and an affine term. "
                + "Four consecutive central-binomial identities give an order-two recurrence for that combination. A shifted operator factorization then yields the six-term recurrence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-a027182"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("mathar-a027182-" + (name == "T" ? "row" : name)), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula IntCast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Integers()));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Choose(Formula n, Formula k) => Apply(Qualified("Nat", "choose"), n, k);
    private static Formula Call(string name, params Formula[] arguments) => Apply(F.Id(name), arguments);

    private static Formula TSmallFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(All("n", Naturals(), All("k", Naturals(), Equal(Call("t", n, k),
            Add(Add(Add(Choose(Add(n, D(2)), Add(k, D(1))), Choose(Add(n, D(1)), k)),
                Choose(Add(n, D(1)), Add(k, D(1)))), Choose(n, k))))));
    }

    private static Formula TFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(All("n", Naturals(), All("k", Naturals(), Equal(Call("T", n, k),
            Add(Subtract(Call("t", n, k), Call("t", D(0), D(0))), D(1))))));
    }

    private static Formula GFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        var range = Apply(Qualified("Finset", "range"), Add(n, D(1)));
        var monomial = Multiply(Apply(Qualified("Polynomial", "C"), Call("T", n, k)),
            new Formula.Power(Qualified("Polynomial", "X"), k));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, range)), Sp, monomial);
        return Disp(All("n", Naturals(), Equal(Call("g", n), sum)));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", Naturals(), Equal(Call("a", n),
            Apply(Qualified("Polynomial", "coeff"), new Formula.Power(Call("g", n), D(2)), n))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), z = IntCast(n);
        var t0 = Multiply(Multiply(D(2), Parenthesized(Add(z, D(2)))), IntCast(Call("a", n)));
        var t1 = Multiply(Parenthesized(Subtract(Multiply(Seq(Minus, D(1,7)), z), D(2,3))),
            IntCast(Call("a", Subtract(n, D(1)))));
        var t2 = Multiply(Parenthesized(Add(Multiply(D(4,7), z), D(3,6))), IntCast(Call("a", Subtract(n, D(2)))));
        var t3 = Multiply(Multiply(D(2), Parenthesized(Subtract(Multiply(Seq(Minus, D(2,2)), z), D(1,7)))),
            IntCast(Call("a", Subtract(n, D(3)))));
        var t4 = Multiply(Multiply(D(4), Parenthesized(Add(Seq(Minus, z), D(2,0)))),
            IntCast(Call("a", Subtract(n, D(4)))));
        var t5 = Multiply(Multiply(D(8), Parenthesized(Subtract(Multiply(D(2), z), D(9)))),
            IntCast(Call("a", Subtract(n, D(5)))));
        var forcing = Multiply(D(2,4), Parenthesized(Subtract(Multiply(D(1,2), z), D(4,7))));
        var sum = Add(Add(Add(Add(Add(Add(t0, t1), t2), t3), t4), t5), forcing);
        return All("n", Naturals(), new Formula.Logic(
            new Formula.Relation(D(6), FormulaRelationOperator.LessThanOrEqual, n),
            FormulaLogicOperator.Implies, Parenthesized(Equal(sum, D(0)))));
    }
}
