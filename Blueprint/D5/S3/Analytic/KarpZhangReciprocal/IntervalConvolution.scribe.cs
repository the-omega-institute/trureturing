using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangReciprocal;

internal sealed class IntervalConvolutionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balancing positive parameters in reciprocal Pochhammer interval convolutions.",
        H("Symmetric interval convolutions"), Blocks(
            CoeffEntry("karp-zhang-reciprocal-coefficient", "c", "Reciprocal coefficients",
                "For every natural n and real t, c(n,t) is the evaluation of ascPochhammer at 2t divided by the product of its evaluation at t and n factorial. For t positive this is the coefficient (2t)n/((t)n n!) in the reciprocal series of Conjecture 5.2, page 12.", DescribeRole.Definition),
            CoeffEntry("karp-zhang-reciprocal-ratio", "lambda", "Adjacent degree ratio",
                "For every natural j and real t, lambda(j,t) equals (2t+j)/(t+j).", DescribeRole.Definition),
            CoeffEntry("karp-zhang-reciprocal-score-increment", "eta", "Score increment",
                "For every natural j and real t, eta(j,t) equals j/((2t+j)(t+j)). In particular the increment at j=0 is zero.", DescribeRole.Definition),
            CoeffEntry("karp-zhang-reciprocal-score", "psi", "Finite score sum",
                "For every natural n and real t, psi(n,t) is the sum of eta(j,t) over 0 <= j < n. The zero index contributes zero, so this equals the sum over 1 <= j < n.", DescribeRole.Definition),
            CoeffEntry("karp-zhang-reciprocal-curvature", "chi", "Finite curvature sum",
                "For every natural n and real t, chi(n,t) is the sum over 0 <= j < n of j(4t+3j)/((2t+j)^2(t+j)^2).", DescribeRole.Definition),
            CoeffEntry("karp-zhang-reciprocal-coefficient-calculus", "coefficient_calculus", "Uniform score and curvature estimates",
                "For every natural n and positive real t, c(n,t) and lambda(n,t) are positive; c(n+1,t)/c(n,t) equals lambda(n,t)/(n+1); the derivative of c(n,t) is c(n,t)psi(n,t), the derivative of psi(n,t) is -chi(n,t). Curvature is nonnegative and at least n times eta(n-1,t) squared. The function j -> lambda(j,t) is antitone. Natural subtraction makes the n=0 curvature estimate meaningful, with both sides zero.", DescribeRole.Theorem),
            Entry("karp-zhang-reciprocal-interval-convolution", "F", "Interval convolution",
                "For natural m, L, U and real s, t, F(m,L,U,s,t) is the sum of c(L+i,s)c(m-(L+i),t) over 0 <= i < U-L+1, with natural subtraction. When L <= U <= m this is exactly the convolution over L <= k <= U.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-symmetric-tail", "symmetric_tail", "Balancing inequality",
                "For every natural m and q with 2q <= m, and reals 0 < a <= b <= c <= d satisfying a+d=b+c, F(m,q,m-q,a,d) <= F(m,q,m-q,b,c). Singleton intervals and equal parameters are included. This proves the symmetric-tail inequality needed for the reciprocal-Pochhammer half of Conjecture 5.2; it makes no assertion about the other half.", DescribeRole.Theorem),
            Entry("karp-zhang-reciprocal-shift-tail", "shift_tail", "Arbitrary nonnegative shifts",
                "For every natural m and q with 2q <= m, positive real mu, and nonnegative real alpha and beta, F(m,q,m-q,mu,mu+alpha+beta) <= F(m,q,m-q,mu+alpha,mu+beta). The shifts need not be ordered. This is the tail estimate consumed by the Abel reduction.", DescribeRole.Theorem),
            Paragraph(Text(
                "On a translated interval 0,...,n, normalize the positive coefficient products to probabilities. Use birth rate (m-k)lambda(k,s) below the upper endpoint and death rate k lambda(m-k,t) above the lower endpoint, with zero outward rates. The coefficient recurrence gives detailed balance. Antitonicity of lambda bounds edge curvature below by lambda(k,s)+lambda(m-k-1,t). The finite birth-and-death variance bound, a weighted square inequality, and chi(j,t) >= j eta(j-1,t)^2 absorb score variance into expected curvature. Differentiating log F(s,S-s) twice therefore gives a nonpositive second derivative. Mathlib's concavity criterion applies on the open interval (0,S). Reindexing k to m-k makes the two endpoint values equal, and the minimum principle for a concave function gives the balancing inequality.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution." + name),
            H(title), TheoremStatement(name), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);

    private static StatementSource TheoremStatement(string name) =>
        name == "F" ? StatementSource.FromAuthor(Disp(All("m", F.Id("Nat"), All("L", F.Id("Nat"), All("U", F.Id("Nat"), All("s", F.Id("Real"), All("t", F.Id("Real"), Equal(Call("F", F.Id("m"), F.Id("L"), F.Id("U"), F.Id("s"), F.Id("t")), SumRange("i", Add(Subtract(F.Id("U"), F.Id("L")), Num(1)), Multiply(Call("c", Add(F.Id("L"), F.Id("i")), F.Id("s")), Call("c", Subtract(F.Id("m"), Add(F.Id("L"), F.Id("i"))), F.Id("t")))))))))))) :
        name == "symmetric_tail" ? StatementSource.FromAuthor(Disp(All("m", F.Id("Nat"), All("q", F.Id("Nat"), Implies(Le(Multiply(Num(2), F.Id("q")), F.Id("m")), All("a", F.Id("Real"), All("b", F.Id("Real"), All("c", F.Id("Real"), All("d", F.Id("Real"), Implies(Lt(Num(0), F.Id("a")), Implies(Le(F.Id("a"), F.Id("b")), Implies(Le(F.Id("b"), F.Id("c")), Implies(Le(F.Id("c"), F.Id("d")), Implies(Equal(Add(F.Id("a"), F.Id("d")), Add(F.Id("b"), F.Id("c"))), Le(Call("F", F.Id("m"), F.Id("q"), Subtract(F.Id("m"), F.Id("q")), F.Id("a"), F.Id("d")), Call("F", F.Id("m"), F.Id("q"), Subtract(F.Id("m"), F.Id("q")), F.Id("b"), F.Id("c"))))))))))))))))) :
        name == "shift_tail" ? StatementSource.FromAuthor(Disp(All("m", F.Id("Nat"), All("q", F.Id("Nat"), Implies(Le(Multiply(Num(2), F.Id("q")), F.Id("m")), All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("mu")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), Le(Call("F", F.Id("m"), F.Id("q"), Subtract(F.Id("m"), F.Id("q")), F.Id("mu"), Add(Add(F.Id("mu"), F.Id("alpha")), F.Id("beta"))), Call("F", F.Id("m"), F.Id("q"), Subtract(F.Id("m"), F.Id("q")), Add(F.Id("mu"), F.Id("alpha")), Add(F.Id("mu"), F.Id("beta"))))))))))))))) :
        StatementSource.WithoutFormula();

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static DocumentBlock CoeffEntry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution." + name),
            H(title), CoeffEntryStatement(name),
            name == "c" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);

    private static StatementSource CoeffEntryStatement(string name) =>
        name == "chi" ? StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), All("t", F.Id("Real"), Equal(Call("chi", F.Id("n"), F.Id("t")), SumRange("j", F.Id("n"), new Formula.Fraction(Multiply(F.Id("j"), Add(Multiply(Num(4), F.Id("t")), Multiply(Num(3), F.Id("j")))), Multiply(new Formula.Power(Add(Multiply(Num(2), F.Id("t")), F.Id("j")), Num(2)), new Formula.Power(Add(F.Id("t"), F.Id("j")), Num(2)))))))))) :
        name == "psi" ? StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), All("t", F.Id("Real"), Equal(Call("psi", F.Id("n"), F.Id("t")), SumRange("j", F.Id("n"), Call("eta", F.Id("j"), F.Id("t")))))))) :
        name == "eta" ? StatementSource.FromAuthor(Disp(All("j", F.Id("Nat"), All("t", F.Id("Real"), Equal(Call("eta", F.Id("j"), F.Id("t")), new Formula.Fraction(F.Id("j"), Multiply(Add(Multiply(Num(2), F.Id("t")), F.Id("j")), Add(F.Id("t"), F.Id("j"))))))))) :
        name == "lambda" ? StatementSource.FromAuthor(Disp(All("j", F.Id("Nat"), All("t", F.Id("Real"), Equal(Call("lambda", F.Id("j"), F.Id("t")), new Formula.Fraction(Add(Multiply(Num(2), F.Id("t")), F.Id("j")), Add(F.Id("t"), F.Id("j")))))))) :
        name == "c" ? StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), All("t", F.Id("Real"), Equal(Call("c", F.Id("n"), F.Id("t")), new Formula.Fraction(App(Qualified("Polynomial", "eval"), Multiply(Num(2), F.Id("t")), Call("ascPochhammer", F.Id("Real"), F.Id("n"))), Multiply(App(Qualified("Polynomial", "eval"), F.Id("t"), Call("ascPochhammer", F.Id("Real"), F.Id("n"))), App(Qualified("Nat", "factorial"), F.Id("n"))))))))) :
        name == "coefficient_calculus" ? StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), All("t", F.Id("Real"), Implies(Lt(Num(0), F.Id("t")), And(Lt(Num(0), Call("c", F.Id("n"), F.Id("t"))), And(Lt(Num(0), Call("lambda", F.Id("n"), F.Id("t"))), And(Equal(new Formula.Fraction(Call("c", Add(F.Id("n"), Num(1)), F.Id("t")), Call("c", F.Id("n"), F.Id("t"))), new Formula.Fraction(Call("lambda", F.Id("n"), F.Id("t")), Add(F.Id("n"), Num(1)))), And(Call("HasDerivAt", Call("c", F.Id("n")), Multiply(Call("c", F.Id("n"), F.Id("t")), Call("psi", F.Id("n"), F.Id("t"))), F.Id("t")), And(Call("HasDerivAt", Call("psi", F.Id("n")), new Formula.Negate(Call("chi", F.Id("n"), F.Id("t"))), F.Id("t")), And(Le(Num(0), Call("chi", F.Id("n"), F.Id("t"))), And(Le(Multiply(F.Id("n"), new Formula.Power(Call("eta", Subtract(F.Id("n"), Num(1)), F.Id("t")), Num(2))), Call("chi", F.Id("n"), F.Id("t"))), Call("Antitone", LambdaOf("j", Call("lambda", F.Id("j"), F.Id("t")))))))))))))))) :
        StatementSource.WithoutFormula();

    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula SumRange(string name, Formula upper, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(F.Id(name), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), upper)), Sp, Parenthesized(body));

    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula LambdaOf(string name, Formula body) =>
        Seq(Operatorname, Grp(F.Id("fun")), Sp, Parenthesized(Seq(F.Id(name), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, body);
}
