using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive transformation and the gamma-series half of Conjecture 5.2.",
        H("From the two-variable transform to the gamma series"), Blocks(
            Entry("karp-zhang-gamma-series-coefficient", "gammaCoeff", "Literal gamma-series coefficients",
                "For real t and natural n, gammaCoeff(t,n) is Real.Gamma(t+n) divided by the product of Real.Gamma(2t+n) and n factorial. The degree-n coefficient of the gamma series is y(n) times gammaCoeff(t,n), as defined before Conjecture 5.2 on page 12 of Karp and Zhang.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-series-scale", "scale", "Positive parameter factor",
                "For real t, scale(t) is Real.sqrt(Real.pi) times 2 to the real power 1-2t. It is positive for every real t. Its products obey scale(t+alpha)scale(t+beta)=scale(t)scale(t+alpha+beta), and scale(t+1)=scale(t)/4.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-positive-beta-transform", "positive_beta_transform", "The finite positive beta transformation",
                "For every natural n and positive real t, gammaCoeff(t,n) equals scale(t) times the sum over j=0,...,floor(n/2) of the reciprocal of (n-2j) factorial times j factorial times Real.Gamma(t+1/2+j) times 2 to the natural power n-2j times 16 to the natural power j. This is positive_beta_transform in finite coefficient form. Strong induction in n is simultaneous in every positive t. Gamma duplication supplies degree zero, Gamma recurrence supplies degree one, and both sides obey the same two-step recurrence involving t+1. There is no convergence hypothesis.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-transform-coefficient", "transformCoeff", "The positive diagonal substitution",
                "For a real sequence y, real a and natural n, transformCoeff(y,a,n) is the sum over j=0,...,floor(n/2) of y(n) divided by (n-2j) factorial times j factorial times Real.Gamma(a+j) times 2 to the natural power n-2j times 16 to the natural power j. It is the degree-n coefficient obtained from H(a;z,w) by substituting z=x/2 and w=x squared/16. The relation r+2j=n ensures that only finitely many bidegrees contribute.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-series-identification", "series_identification", "Identification with the transformed series",
                "For every real sequence y, positive real t and natural n, y(n)gammaCoeff(t,n)=scale(t)transformCoeff(y,t+1/2,n). This coefficient identity proves the formal series identification with no restriction on growth, signs or log-concavity of y. It follows by multiplying positive_beta_transform by y(n).", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-series-delta", "gammaDelta", "Finite Cauchy coefficient of the gamma Turanian",
                "For a real sequence y, real mu,alpha,beta and natural n, gammaDelta(y,mu,alpha,beta,n) is the sum over k=0,...,n of y(k)gammaCoeff(mu+alpha,k)y(n-k)gammaCoeff(mu+beta,n-k) minus y(k)gammaCoeff(mu,k)y(n-k)gammaCoeff(mu+alpha+beta,n-k). This is the literal degree-n Cauchy coefficient of the gamma-series Turanian.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-half", "gamma_half", "Every coefficient of the gamma-series Turanian is nonnegative",
                "For every real sequence y satisfying D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave, every positive real mu, all nonnegative real alpha,beta and every natural n, gammaDelta(y,mu,alpha,beta,n) is nonnegative. The existing predicate includes nonnegativity and no internal zeros. No shift-integrality, convergence or growth assumption is added. Apply series_identification to the four factors, cancel their common positive scale product, and use the finite diagonal Cauchy identity. The remaining coefficient is the sum over m=0,...,floor(n/2) of Result.transformDelta(y,mu+1/2,alpha,beta,n-2m,m) divided by 2 to the natural power n-2m times 16 to the natural power m. Every summand is nonnegative by Result.two_variable_nonneg.", DescribeRole.Theorem),
            Paragraph(Text("The scalar recurrence for the diagonal transform is (n+2)T(a,n+2)=T(a,n+1)/2+T(a+1,n)/8. The literal gamma coefficient satisfies (n+2)gammaCoeff(t,n+2)=gammaCoeff(t,n+1)/2+gammaCoeff(t+1,n)/2. The factor scale(t+1)=scale(t)/4 aligns these recurrences. Finite fibers r+2j=n justify the Euler-degree identity and every reindexing. For products, the index map sends (k,i,j) to (i+j,i,k-2i), with inverse (m,i,r) maps to (r+2i,i,m-i). This identifies the coefficient of the substituted product with the positive weighted sum of its bivariate coefficients.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Series." + name),
            H(title), TheoremStatement(name),
            name == "gammaCoeff" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);

    private static StatementSource TheoremStatement(string name) =>
        name == "gammaDelta" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), All("n", F.Id("Nat"), Equal(Call("gammaDelta", F.Id("y"), F.Id("mu"), F.Id("alpha"), F.Id("beta"), F.Id("n")), SumRange("k", Add(F.Id("n"), Num(1)), Subtract(Multiply(Multiply(App(F.Id("y"), F.Id("k")), Call("gammaCoeff", Add(F.Id("mu"), F.Id("alpha")), F.Id("k"))), Multiply(App(F.Id("y"), Subtract(F.Id("n"), F.Id("k"))), Call("gammaCoeff", Add(F.Id("mu"), F.Id("beta")), Subtract(F.Id("n"), F.Id("k"))))), Multiply(Multiply(App(F.Id("y"), F.Id("k")), Call("gammaCoeff", F.Id("mu"), F.Id("k"))), Multiply(App(F.Id("y"), Subtract(F.Id("n"), F.Id("k"))), Call("gammaCoeff", Add(Add(F.Id("mu"), F.Id("alpha")), F.Id("beta")), Subtract(F.Id("n"), F.Id("k"))))))))))))))) :
        name == "transformCoeff" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("a", F.Id("Real"), All("n", F.Id("Nat"), Equal(Call("transformCoeff", F.Id("y"), F.Id("a"), F.Id("n")), SumRange("j", Add(App(Qualified("Nat", "div"), F.Id("n"), Num(2)), Num(1)), new Formula.Fraction(App(F.Id("y"), F.Id("n")), Multiply(Multiply(Multiply(Multiply(App(Qualified("Nat", "factorial"), Subtract(F.Id("n"), Multiply(Num(2), F.Id("j")))), App(Qualified("Nat", "factorial"), F.Id("j"))), App(Qualified("Real", "Gamma"), Add(F.Id("a"), F.Id("j")))), new Formula.Power(Num(2), Subtract(F.Id("n"), Multiply(Num(2), F.Id("j"))))), new Formula.Power(Num(16), F.Id("j"))))))))))) :
        name == "scale" ? StatementSource.FromAuthor(Disp(All("t", F.Id("Real"), Equal(Call("scale", F.Id("t")), Multiply(App(Qualified("Real", "sqrt"), Qualified("Real", "pi")), new Formula.Power(Num(2), Subtract(Num(1), Multiply(Num(2), F.Id("t"))))))))) :
        name == "gammaCoeff" ? StatementSource.FromAuthor(Disp(All("t", F.Id("Real"), All("n", F.Id("Nat"), Equal(Call("gammaCoeff", F.Id("t"), F.Id("n")), new Formula.Fraction(App(Qualified("Real", "Gamma"), Add(F.Id("t"), F.Id("n"))), Multiply(App(Qualified("Real", "Gamma"), Add(Multiply(Num(2), F.Id("t")), F.Id("n"))), App(Qualified("Nat", "factorial"), F.Id("n"))))))))) :
        name == "positive_beta_transform" ? StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), All("t", F.Id("Real"), Implies(Lt(Num(0), F.Id("t")), Equal(Call("gammaCoeff", F.Id("t"), F.Id("n")), Multiply(Call("scale", F.Id("t")), SumRange("j", Add(App(Qualified("Nat", "div"), F.Id("n"), Num(2)), Num(1)), new Formula.Fraction(Num(1), Multiply(Multiply(Multiply(Multiply(App(Qualified("Nat", "factorial"), Subtract(F.Id("n"), Multiply(Num(2), F.Id("j")))), App(Qualified("Nat", "factorial"), F.Id("j"))), App(Qualified("Real", "Gamma"), Add(Add(F.Id("t"), new Formula.Fraction(Num(1), Num(2))), F.Id("j")))), new Formula.Power(Num(2), Subtract(F.Id("n"), Multiply(Num(2), F.Id("j"))))), new Formula.Power(Num(16), F.Id("j")))))))))))) :
        name == "series_identification" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("t", F.Id("Real"), Implies(Lt(Num(0), F.Id("t")), All("n", F.Id("Nat"), Equal(Multiply(App(F.Id("y"), F.Id("n")), Call("gammaCoeff", F.Id("t"), F.Id("n"))), Multiply(Call("scale", F.Id("t")), Call("transformCoeff", F.Id("y"), Add(F.Id("t"), new Formula.Fraction(Num(1), Num(2))), F.Id("n")))))))))) :
        name == "gamma_half" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(Call("IsLogConcave", F.Id("y")), All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("mu")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), All("n", F.Id("Nat"), Le(Num(0), Call("gammaDelta", F.Id("y"), F.Id("mu"), F.Id("alpha"), F.Id("beta"), F.Id("n")))))))))))))) :
        StatementSource.WithoutFormula();

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula SumRange(string name, Formula upper, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(F.Id(name), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), upper)), Sp, Parenthesized(body));
}
