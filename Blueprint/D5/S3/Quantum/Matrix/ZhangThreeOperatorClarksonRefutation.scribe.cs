using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ZhangThreeOperatorClarksonRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/zhang2024clarksonmccarthy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three complex matrices of order two violate the three-operator Clarkson–McCarthy inequality at exponent nine quarters.",
        H("A counterexample to the three-operator Clarkson–McCarthy inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhang-three-operator-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The inequality for real exponents at least two"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The assertion quantifies over every real p at least two, every natural dimension n, "
                        + "and three complex n by n matrices a, b, c. The sum of the pth powers of the "
                        + "Schatten norms of a+b+c, a, b and c is bounded above by "
                        + "(3^(p−1)+1)/2^p times the corresponding sum for a+b, b+c and c+a. "
                        + "Here schattenNorm is the trace-functional-calculus Schatten norm; for positive p, "
                        + "its pth power is the sum of the pth powers of the singular values. "
                        + "The source defines the Schatten norm in lines 100–104 and states the conjecture "
                        + "labeled conj:sharp-inequality in lines 571–581 of its TeX source. This assertion "
                        + "is its finite complex matrix reading for p at least two. The reverse inequality "
                        + "for positive p at most two is a separate assertion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zhang-three-operator-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A counterexample at exponent nine quarters"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a complex matrix x of order two and a nonnegative real vector d, suppose "
                            + "the Gram matrix x*x has the same characteristic polynomial as the diagonal "
                            + "matrix with entries d, included in the complex numbers. Here x* denotes "
                            + "conjugate transpose. Both matrices are Hermitian, so their ordered eigenvalue "
                            + "vectors agree. Unitary similarity of the diagonal matrix with itself gives "
                            + "a permutation matching its eigenvalues to d. Reindexing the singular-value "
                            + "sum by this permutation and using nonnegativity of d shows that, for every "
                            + "p>0, the pth power of the Schatten norm of x is the sum of d(i)^(p/2).")),
                    Paragraph(Text(
                        "Take A=coordinateProjectorTwo 0=diag(1,0), B=diag(0,1), and C=−(1/2)[[1,1],[1,1]]. "
                            + "Then A+B+C=(1/2)[[1,−1],[−1,1]]. The Gram matrices of A, B, C and "
                            + "A+B+C each have the characteristic polynomial of diag(1,0). Applying the "
                            + "preceding calculation with d=(1,0) shows that each of these four matrices "
                            + "has Schatten norm to the power p equal to one for every p>0. "
                            + "The left side of the asserted inequality is therefore four.")),
                    Paragraph(Text(
                        "The Gram matrix of A+B=I is I. The calculation with the constant vector "
                            + "d=(1,1) gives Schatten norm to the power p equal to two. The Gram matrices "
                            + "of B+C and C+A are each (1/2)I. Applying the calculation with "
                            + "d=(1/2,1/2) gives 2(1/2)^(p/2) for each. The sum for the three pairwise "
                            + "sums is thus 2+4(1/2)^(p/2)=2+2^(2−p/2).")),
                    Paragraph(Text(
                        "At p=9/4, positive real power laws give (3^(1/4))^4=3, "
                            + "(2^(1/4))^4=2, and (2^(7/8))^8=128. Comparing fourth and eighth "
                            + "powers of nonnegative numbers yields 3^(1/4)<13161/10000, "
                            + "11892/10000<2^(1/4), and 2^(7/8)<18341/10000. "
                            + "Rewrite 3^(9/4−1)=3·3^(1/4), 2^(9/4)=4·2^(1/4), and "
                            + "2−(9/4)/2=7/8. After clearing the positive denominator, the desired "
                            + "strict upper bound by four reduces to "
                            + "(3·3^(1/4)+1)(2+2^(7/8))<16·2^(1/4). Successively replacing the "
                            + "two factors on the left by their rational upper bounds gives "
                            + "(3·13161/10000+1)(2+18341/10000)<16·11892/10000<16·2^(1/4). "
                            + "The rational strict inequality follows by exact arithmetic.")),
                    Paragraph(Text(
                        "If the assertion held, its instance at p=9/4, n=2, a=A, b=B and c=C "
                            + "would give 4≤((3^(9/4−1)+1)/2^(9/4))(2+2^(7/8)). "
                            + "The strict bound just established makes that right side smaller than four, "
                            + "a contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-2024-three-operator-clarkson-mccarthy"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula left = Add(Add(Add(SchattenPower(Add(Add(a, b), c), p),
            SchattenPower(a, p)), SchattenPower(b, p)), SchattenPower(c, p));
        Formula coefficient = new Formula.Fraction(
            Add(new Formula.Power(Typed(D(3), Reals()), Subtract(p, Typed(D(1), Reals()))),
                Typed(D(1), Reals())),
            new Formula.Power(Typed(D(2), Reals()), p));
        Formula pairs = Add(Add(SchattenPower(Add(a, b), p), SchattenPower(Add(b, c), p)),
            SchattenPower(Add(c, a), p));
        Formula matrices = All("n", Naturals(), All("a", MatrixType(), All("b", MatrixType(),
            All("c", MatrixType(), LE(left, Multiply(coefficient, pairs))))));
        return Equivalence(Local("claim"), All("p", Reals(),
            Arrow(LE(Typed(D(2), Reals()), p), matrices)));
    }

    private static Formula SchattenPower(Formula matrix, Formula p) =>
        new Formula.Power(At(Qualified("schattenNorm"), matrix, p), p);
    private static Formula MatrixType() => At(Qualified("Matrix"),
        At(Qualified("Fin"), F.Id("n")), At(Qualified("Fin"), F.Id("n")), Complexes());
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Matrix",
        "ZhangThreeOperatorClarksonRefutation", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
