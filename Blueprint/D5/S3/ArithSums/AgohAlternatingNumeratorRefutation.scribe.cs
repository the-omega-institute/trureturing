using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class AgohAlternatingNumeratorRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/agoh2026intrinsic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A repeated real root is compatible with every alternating numerator factor.",
        H("Agoh's alternating-numerator characterization is false"),
        Blocks(
            Node("Q", "The literal rational sum", QFormula(),
                "For a real polynomial f and a natural n, Q(f,n) is the alternating "
                + "sum from i=0 through n of (-1)^i choose(n,i)/f(X^i), in the "
                + "field of real rational functions. This is Equation (3.1). "
                + "Polynomial composition supplies f(X^i). Every denominator "
                + "polynomial is nonzero for the counterexample below.", DescribeRole.Definition),
            Node("NumeratorProperty", "An all-order reduced-numerator property", PropertyFormula(),
                "The quantifier includes every natural n, including zero. The num "
                + "operation is the reduced rational-function numerator, not the "
                + "numerator produced by an arbitrary common denominator.", DescribeRole.Definition),
            Node("IsMonomial", "The monomial alternative", MonomialFormula(),
                "A monomial has one nonzero real coefficient a at a natural degree d. "
                + "Constants are included by d=0.", DescribeRole.Definition),
            Node("SimpleRootsAwayFromOne", "The simple-root alternative", SimpleFormula(),
                "Every real root must have multiplicity exactly one and be different "
                + "from one. This predicate is used only on nonzero splitting polynomials.",
                DescribeRole.Definition),
            Node("fullClaim", "The full conjectured equivalence", ClaimFormula(),
                "RealPolynomial denotes polynomials over the real numbers. Splits "
                + "means real-rooted. The all-order numerator property is kept inside "
                + "the equivalence for each nonzero real-rooted f. The source's "
                + "Section 3 also assumes f nonconstant and f(1) nonzero; the "
                + "counterexample satisfies both conditions.", DescribeRole.Definition),
            Node("coefficientDigit", "Base-nine coefficient decoding", null,
                "A number below 729 contains three base-nine digits. The digit at "
                + "index i is the quotient by 9^i reduced modulo 9.", DescribeRole.Definition),
            Node("actualCode", "The actual coefficient code", null,
                "The code 413 has base-nine digits [8,0,5], from least to most "
                + "significant.", DescribeRole.Definition),
            Node("actualWord", "The actual coefficient word", null,
                "Reading the three digits of 413 gives [8,0,5]. Subtracting four "
                + "from each digit gives coefficients [4,-4,1].", DescribeRole.Definition),
            Node("actualCoefficientReadout", "The three coefficient readings", null,
                "The readings at indices zero, one and two are respectively 8, 0 "
                + "and 5, exactly the three base-nine digits of 413.", DescribeRole.Definition),
            Node("decodeCode", "Signed coefficient decoding", null,
                "Decode a code c by the real number val(c)-4.", DescribeRole.Definition),
            Node("polynomialOfWord", "Reconstructing the polynomial", null,
                "Sum C(decode(word(i))) times X^i over the three indices. The "
                + "actual word reconstructs 4-4X+X^2=(X-2)^2.", DescribeRole.Definition),
            Node("CounterexampleCertificate", "The complete algebraic certificate", null,
                "The certificate requires nonzero, splitting, nonconstant, value "
                + "one at X=1, the reduced-numerator property for every natural n, "
                + "not monomial, and failure of the simple-root alternative.", DescribeRole.Definition),
            Node("coefficientArena", "Reading the counterexample coefficients", null,
                "A state is one code below 729, representing exactly three base-nine "
                + "digits. The law requires that reading code 413 returns its three "
                + "digits, together with the complete algebraic certificate for the "
                + "decoded coefficient word.", DescribeRole.Definition),
            Node("actualRealization", "Three coefficient readings", null,
                "At each index the readout returns the corresponding digit of code "
                + "413. Each of the three readings can change independently.", DescribeRole.Definition),
            Node("result", "The full characterization is false",
                F.Disp(new Formula.Not(F.Id("fullClaim"))),
                "Take f=(X-2)^2. It is nonzero, real-rooted and nonconstant, with "
                + "f(1)=1. For each n let t_i=f(X^i), D be their indexed product, "
                + "and N the weighted sum of products deleting index i. In an "
                + "auxiliary variable Y, the coefficient of degree k+1 in "
                + "product_j(Y+t_j) is the elementary symmetric polynomial of "
                + "degree n-k. Coefficient telescoping therefore gives the "
                + "indexed deletion identity of Equation (2.3). It preserves "
                + "repeated values by deleting indices rather than polynomial values. "
                + "Expanding f^k by its coefficients and applying the binomial "
                + "theorem changes each inner alternating sum into a sum of "
                + "coeff(f^k,r)(1-X^r)^n. The remainder theorem shows X-1 "
                + "divides each 1-X^r, so (X-1)^n divides N. This includes n=0. "
                + "All t_i evaluate to one at X=1, so D is nonzero and D(1)=1. "
                + "The literal rational sum equals N/D, and the reduced fraction "
                + "identity yields num(Q)D=N denom(Q). An explicit Bezout identity "
                + "makes (X-1)^n coprime to D and cancels D, proving the property "
                + "for the actual reduced numerator. The nonzero coefficients 4 and "
                + "-4 rule out a monomial, while root 2 has multiplicity 2. Hence "
                + "this nonconstant polynomial satisfies the all-order property but "
                + "neither alternative in the conjectured characterization, so the "
                + "full equivalence is false.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("agoh-alternating-numerator-characterization"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula? statement,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("agoh-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            statement is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(statement),
            name is "Q" or "NumeratorProperty" or "IsMonomial" or "SimpleRootsAwayFromOne" or "fullClaim"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula QFormula()
    {
        var f = F.Id("f"); var n = F.Id("n"); var i = F.Id("i");
        var weight = Multiply(Power(Parens(Subtract(F.D(0), F.D(1))), i), Call("choose", n, i));
        var sum = F.Seq(F.Sum, F.Underscore, F.Grp(Equal(i, F.D(0))), F.Caret, F.Grp(n),
            new Formula.Fraction(weight, Call("f", Power(F.Id("X"), i))));
        return F.Disp(Equal(Call("Q", f, n), sum));
    }

    private static Formula PropertyFormula()
    {
        var f = F.Id("f"); var n = F.Id("n");
        return F.Disp(Iff(Call("NumeratorProperty", f), Bound("n", "Nat",
            Divides(Power(Parens(Subtract(F.Id("X"), F.D(1))), n), Call("num", Call("Q", f, n))))));
    }

    private static Formula MonomialFormula()
    {
        var f = F.Id("f"); var d = F.Id("d"); var a = F.Id("a");
        return F.Disp(Iff(Call("IsMonomial", f), Exists("d", "Nat", Exists("a", "Real",
            And(new Formula.Relation(a, FormulaRelationOperator.NotEqual, F.D(0)),
                Equal(f, Call("monomial", d, a)))))));
    }

    private static Formula SimpleFormula()
    {
        var f = F.Id("f"); var a = F.Id("a");
        return F.Disp(Iff(Call("SimpleRootsAwayFromOne", f), Bound("a", "Real",
            Implies(Call("IsRoot", f, a), And(Equal(Call("rootMultiplicity", f, a), F.D(1)),
                new Formula.Relation(a, FormulaRelationOperator.NotEqual, F.D(1)))))));
    }

    private static Formula ClaimFormula()
    {
        var f = F.Id("f");
        return F.Disp(Iff(F.Id("fullClaim"), Bound("f", "RealPolynomial", Implies(
            And(new Formula.Relation(f, FormulaRelationOperator.NotEqual, F.D(0)), Call("Splits", f)),
            Iff(Call("NumeratorProperty", f), new Formula.Logic(Call("IsMonomial", f),
                FormulaLogicOperator.Or, Call("SimpleRootsAwayFromOne", f)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Bound(string name, string domain, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), F.Id(domain), body);
    private static Formula Exists(string name, string domain, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), F.Id(domain), body);
    private static Formula Parens(Formula x) => F.Seq(F.Open, x, F.Close);
    private static Formula Power(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Divides(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Multiply(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parens(x), FormulaLogicOperator.And, Parens(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parens(x), FormulaLogicOperator.Iff, Parens(y));
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(Parens(x), FormulaLogicOperator.Implies, Parens(y));
}
