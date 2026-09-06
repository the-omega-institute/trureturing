using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.PochhammerDeformation;

internal sealed class QuadraticIntervalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/vishnyakova2026polynomially");
    private static Formula A => F.Id("a");
    private static Formula T => F.Id("t");
    private static Formula X => F.Id("X");
    private static Formula Radical => Seq(Sqrt, Grp(Square(A), Plus, A));
    private static Formula Radius => Quot(Seq(Radical, Minus, A), D(2));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized Pochhammer operator has an exact degree-two real-root interval; "
            + "its leftward extent violates the proposed strict upper bound for small positive parameters.",
        H("Quadratic Pochhammer Deformation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pochhammer-linear-operator"),
                DeclarationHandle.Create(Prefix + "lOp"),
                H("The normalized falling-Pochhammer operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The operator is constructed as a real linear map on the falling-Pochhammer "
                        + "basis. Its kth basis vector D_k is X(X-1)...(X-k+1), including D_0=1. "
                        + "The rising factor (a)_k is the evaluation at a of Mathlib's ascending "
                        + "Pochhammer polynomial. The construction sends D_k to (a)_k X^k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complex-root-interval-predicate"),
                DeclarationHandle.Create(Prefix + "RealRootsInUnitInterval"),
                H("All complex roots lie in the real interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every member z of the root multiset after mapping the real polynomial's "
                        + "coefficients to the complex numbers, the imaginary part of z is zero "
                        + "and its real part lies in the closed interval [-1,0]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("degree-two-parameter-set"),
                DeclarationHandle.Create(Prefix + "m2"),
                H("The degree-two parameter set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "M_2(a) consists of all real t for which L_a((X+t)^2) satisfies the "
                        + "preceding complex-root predicate. Write Q_{a,t}=L_a((X+t)^2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("leftward-extent"),
                DeclarationHandle.Create(Prefix + "c2"),
                H("Leftward extent from the parameter set"),
                StatementSource.FromAuthor(Disp(Seq(C(A), Eq, Minus,
                    Call("sInf", M(A))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The extent is the negative infimum of M_2(a), defined independently of "
                        + "the square-root formula. The interval theorem proves this infimum "
                        + "is the left endpoint and identifies the conjecture's interval parameter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operator-defining-equation"),
                DeclarationHandle.Create(Prefix + "lOp_definition"),
                H("Definition 1.4 holds for the constructed map"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, A, InMacro, Sp, RealField(), Comma, A, Gt, D(0), Comma,
                    Forall, Sp, F.Id("k"), InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                    L(Quot(Seq(F.Id("D"), Underscore, Grp(F.Id("k"))),
                        Seq(Open, A, Close, Underscore, Grp(F.Id("k"))))), Eq,
                    X, Caret, Grp(F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positivity of a makes every rising Pochhammer factor nonzero. "
                        + "Linearity extends these defining equations to every finite expansion, "
                        + "exactly as in Definition 1.4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-image"),
                DeclarationHandle.Create(Prefix + "lOp_quadratic"),
                H("Explicit quadratic image"),
                StatementSource.FromAuthor(Disp(Seq(Parameters(),
                    L(Square(Seq(Open, X, Plus, T, Close))), Eq,
                    A, Open, A, Plus, D(1), Close, Square(X), Plus,
                    A, Open, D(1), Plus, D(2), T, Close, X, Plus, Square(T)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Expand the input on D_0,D_1,D_2 and apply the normalized defining "
                        + "equation together with linearity. The coefficient formula is a "
                        + "conclusion about the constructed operator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-endpoint-squares"),
                DeclarationHandle.Create(Prefix + "quadratic_endpoint_squares"),
                H("Both endpoint values are squares"),
                StatementSource.FromAuthor(Disp(Seq(Parameters(),
                    Q(D(0)), Eq, Square(T), Geq, Sp, D(0), Comma, Quad, Sp,
                    Q(Seq(Minus, D(1))), Eq, Square(Seq(Open, A, Minus, T, Close)),
                    Geq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The value at -1 is identically (a-t)^2. This equality is used in the "
                        + "interval proof to supply the lower-endpoint sign condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-interval-closed-form"),
                DeclarationHandle.Create(Prefix + "quadratic_interval_closed_form"),
                H("Exact parameter interval and extent"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(PositiveParameter(), M(A), Eq,
                        Interval(Quot(Seq(A, Minus, Radical), D(2)),
                            Quot(Seq(A, Plus, Radical), D(2))), Comma),
                    Seq(C(A), Eq, Radius, Comma, Quad, Sp,
                        M(A), Eq, Interval(Seq(Minus, C(A)), Seq(A, Plus, C(A)))),
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A complex root exists because the leading coefficient is positive and "
                        + "the degree is two. If all complex roots are real, the discriminant "
                        + "is a square. Conversely, a nonnegative discriminant makes each "
                        + "complex root real by the quadratic formula. The endpoint squares "
                        + "and the vertex bounds then place these roots in [-1,0].")),
                    Paragraph(Text(
                        "The discriminant is a(a+4at-4t^2). Its nonnegativity gives the "
                            + "displayed t interval, and sqrt(a^2+a)<a+1 makes the vertex "
                            + "condition automatic. Repeated roots at the two parameter "
                            + "endpoints are included. Thus the conjectured interval shape "
                            + "holds at degree two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-conjecture-refutation"),
                DeclarationHandle.Create(Prefix + "quadratic_conjecture_refutation"),
                H("The strict upper bound fails for all small positive parameters"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(PositiveParameter(), Open, C(A), Lt, D(2), A,
                        Leftrightarrow, Sp, Quot(D(1), D(2,4)), Lt, A, Close, Comma),
                    Seq(C(Quot(D(1), D(2,4))), Eq, Quot(D(1), D(1,2)), Eq,
                        D(2), Cdot, Quot(D(1), D(2,4)), Comma),
                    Seq(Open, A, Leq, Sp, Quot(D(1), D(2,4)), Rightarrow, Sp,
                        Open, D(2), A, Leq, Sp, C(A), Land, Sp,
                        Neg, Sp, Open, D(0), Lt, C(A), Land, Sp, C(A), Lt, D(2), A,
                        Close, Close, Close),
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive a, sqrt(a^2+a)<5a is equivalent to 1/24<a. "
                        + "The boundary equality is an instance of the general closed form. "
                        + "Every 0<a<=1/24 therefore refutes Conjecture 6.5's strict upper "
                        + "bound at k=1. Higher degrees, monotonicity in k, its limit, and "
                        + "the Riemann hypothesis are outside this result."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Call(string name, Formula x) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [x]);
    private static Formula Square(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Quot(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Interval(Formula x, Formula y) =>
        Seq(OpenBracket, x, Comma, y, CloseBracket);
    private static Formula RealField() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula PositiveParameter() =>
        Seq(Forall, Sp, A, InMacro, Sp, RealField(), Comma, A, Gt, D(0), Comma, Quad, Sp);
    private static Formula Parameters() => Seq(PositiveParameter(),
        Forall, Sp, T, InMacro, Sp, RealField(), Comma, Quad, Sp);
    private static Formula L(Formula p) => Apply(Seq(Mathcal, Grp(F.Id("L")), Underscore, Grp(A)), p);
    private static Formula Q(Formula x) => Apply(Seq(F.Id("Q"), Underscore, Grp(A, Comma, T)), x);
    private static Formula C(Formula a) => Apply(Seq(F.Id("c"), Underscore, Grp(D(2))), a);
    private static Formula M(Formula a) => Apply(Seq(F.Id("M"), Underscore, Grp(D(2))), a);
}
