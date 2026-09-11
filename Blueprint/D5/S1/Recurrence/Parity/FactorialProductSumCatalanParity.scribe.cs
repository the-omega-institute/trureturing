using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class FactorialProductSumCatalanParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/FactorialProductSumCatalanParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2024a222013");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A222013 are odd exactly one below a power of two.",
        H("Factorial Product Sum and Catalan Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a222013 specifies a factorial "
                + "product sum for A and conjectures that a(n) is odd exactly when "
                + "n=2^k-1 for some natural k. The conjecture is dated December 6, 2024. "
                + "The equivalent formulation n+1=2^k avoids natural subtraction.")),
            Paragraph(Text("All indices are natural numbers, all unreduced coefficients "
                + "are integers, and X is the indeterminate. A denotes generatingSeries. "
                + "The operator coeff extracts a coefficient, mk constructs a series from "
                + "its coefficient function, and C embeds an integer as a constant series. "
                + "The operator int casts a natural number to an integer; factorial is "
                + "the natural factorial; div is natural integer division. The operator "
                + "invOfUnit takes the indicated series and the integer unit 1. Each "
                + "denominator factor has constant coefficient one. The product indexed "
                + "by k in range(r) uses k+1, hence is exactly the product from 1 to r.")),
            Paragraph(Text("P denotes the local approximations. The finite coefficient "
                + "window is exact because the rth term contains X^r; it expresses the "
                + "infinite sum without an infinite-sum operation on formal series. "
                + "The map pi is Int.castRingHom into ZMod(2), and map(pi,B) reduces "
                + "B coefficientwise. K denotes the integer catalanSeries from "
                + "CatalanCompositionSquareParity, with zero constant coefficient and "
                + "K=X+K^2. Its binary_catalan theorem supplies the binary support.")),
            Node("term", "The factorial product summand", TermFormula(),
                "The numerator is the factorial constant times X^r times the indicated "
                + "power of the input series. Multiplication by invOfUnit implements "
                + "division by the product with constant coefficient one.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", SequenceFormula(),
                "Iteration of the finite-window operator starts at the zero series. "
                + "Agreement below degree n becomes agreement below degree n+1: powers, "
                + "products and unit inverses preserve agreement, and every nonconstant "
                + "summand adds at least one factor X. The diagonal defines a(n).",
                DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", F.Id("a")))),
                "The series is constructed from the diagonal coefficient function a.",
                DescribeRole.Definition),
            Node("term_coeff_eq_zero", "The exact coefficient window", VanishingFormula(),
                "The explicit factor X^r divides the summand. Mathlib's coefficient "
                + "criterion for this divisibility forces every coefficient below r to vanish."),
            Node("generating_equation", "The OEIS equation", EquationFormula(),
                "Stability of the approximations identifies each diagonal coefficient "
                + "with the corresponding coefficient after one further iteration. "
                + "This proves the defining sum and its constant coefficient one."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "Two fixed points agree below degree zero. Applying degree contraction "
                + "inductively gives agreement below every degree, hence equality. "
                + "The coefficient equation also forces the stated normalization."),
            Node("mod_two_equation", "Reduction to the Catalan equation",
                Disp(Equal(Reduce(A()), Add(D(1), Mul(X(), Power(Reduce(A()), D(2)))))),
                "For r at least two, divisibility of r! by two kills the entire summand. "
                + "The remaining terms give C=1+XC invOfUnit(1+XC,1) for C=map(pi,A). "
                + "Multiplication by 1+XC and characteristic two give C=1+XC^2."),
            Node("mod_two_identity", "Identification with binary Catalan support",
                Disp(Equal(Mul(X(), Reduce(A())), Reduce(K()))),
                "Both X map(pi,A) and map(pi,K) have zero constant coefficient and "
                + "satisfy Y=X+Y^2. Their difference times the unit 1-Y-Z is zero, "
                + "so cancellation identifies the two series."),
            Node("hanna_conjecture", "Hanna's parity conjecture", HannaFormula(),
                "Taking coefficient n+1 in the Catalan identity gives the reduction of "
                + "a(n). The imported binary_catalan theorem says this is one precisely "
                + "when n+1 is a power of two. Casting an integer to one in ZMod(2) "
                + "is equivalent to oddness.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a222013-factorial-product-sum-catalan-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a222013-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => F.Id("A");
    private static Formula K() => F.Id("K");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Reduce(Formula series) => Call("map", F.Id("pi"), series);
    private static Formula Window(Formula n, Formula series) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id("r"), Sp, InMacro, Sp,
            Call("range", Add(n, D(1))))), Sp,
        Parenthesized(Call("coeff", n, Call("term", F.Id("r"), series))));
    private static Formula CoefficientEquation(Formula series) =>
        Seq(Bound("N", Naturals()), Equal(Call("coeff", F.Id("N"), series),
            Window(F.Id("N"), series)));

    private static Formula TermFormula()
    {
        Formula r = F.Id("r");
        Formula k = F.Id("k");
        Formula f = F.Id("F");
        Formula next = Add(k, D(1));
        Formula factor = Add(D(1), Mul(Mul(Call("C", Call("int", next)), X()), Power(f, next)));
        Formula product = Seq(new Formula.Subscript(Prod,
            Seq(k, Sp, InMacro, Sp, Call("range", r))), Sp, Parenthesized(factor));
        Formula exponent = Call("div", Mul(r, Parenthesized(Add(r, D(1)))), D(2));
        Formula numerator = Mul(Mul(Call("C", Call("int", Call("factorial", r))), Power(X(), r)),
            Power(f, exponent));
        return Disp(Seq(Bound("r", Naturals()), Bound("F", Series()),
            Equal(Call("term", r, f), Mul(numerator, Call("invOfUnit", product, D(1))))));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula degree = F.Id("N");
        return Disp(new Formula.Aligned([
            Equal(Call("P", D(0)), D(0)),
            Seq(Bound("n", Naturals()), Equal(Call("P", Add(n, D(1))),
                Call("mk", Parenthesized(Seq(degree, Sp, Mapsto, Sp, Window(degree, Call("P", n))))))),
            Seq(Bound("n", Naturals()), Equal(Call("a", n), Call("coeff", n, Call("P", Add(n, D(1))))))
        ]));
    }

    private static Formula VanishingFormula() => Disp(Seq(
        Bound("r", Naturals()), Bound("N", Naturals()),
        Implication(Seq(F.Id("N"), Sp, Lt, Sp, F.Id("r")),
            Seq(Bound("F", Series()), Equal(Call("coeff", F.Id("N"),
                Call("term", F.Id("r"), F.Id("F"))), D(0))))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(1)), CoefficientEquation(A())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(CoefficientEquation(b), Equal(b, A())))));
    }

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Equal(Add(n, D(1)), Power(D(2), k)));
        return Disp(Seq(Bound("n", Naturals()), Call("Odd", Call("a", n)),
            Sp, Iff, Sp, Parenthesized(support)));
    }
}
