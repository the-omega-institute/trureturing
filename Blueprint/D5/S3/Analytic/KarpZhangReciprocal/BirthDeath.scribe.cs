using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangReciprocal;

internal sealed class BirthDeathDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite variance inequality for reversible birth-and-death rates.",
        H("Variance and edge curvature"), Blocks(
            Entry("karp-zhang-birth-death-curvature", "kappa", "Edge curvature",
                "For all real sequences p and r and every natural i, kappa(p,r,i) equals p(i)-p(i+1)+r(i+1)-r(i).", DescribeRole.Definition),
            Entry("karp-zhang-birth-death-variance", "variance", "Finite variance",
                "For a natural n and real sequences pi and h, set a equal to the sum of pi(j)h(j) over 0 <= j <= n. Then variance(n,pi,h) is the sum over 0 <= i <= n of pi(i) times (h(i)-a) squared. Under probability normalization this is the usual variance.", DescribeRole.Definition),
            Entry("karp-zhang-birth-death-variance-bound", "variance_bound", "Curvature-weighted variance bound",
                "Let n be any natural number. Suppose pi is positive on the vertices 0,...,n and sums to one there. Let p(n)=r(0)=0, let p(i)>0 for i<n, and let r(i)>0 for 0<i<=n. Assume detailed balance pi(i)p(i)=pi(i+1)r(i+1) and positive kappa(p,r,i) for every i<n. Then, for every real sequence h, variance(n,pi,h) is at most the sum over 0 <= i < n of pi(i)p(i)/kappa(p,r,i) times (h(i+1)-h(i)) squared. The hypotheses allow n=0, when the variance and the edge sum vanish.", DescribeRole.Theorem),
            Paragraph(Text(
            "Center h by its pi mean. An edge flux z is obtained by taking the negative cumulative centered mass and dividing by the edge weight. It satisfies h(i)=r(i)z(i)-p(i)z(i+1). Detailed balance converts the variance into the edge sum of pi(i)p(i)(h(i+1)-h(i))z(i+1). A pointwise square inequality and the same balance identity bound the sum of pi(i)p(i)kappa(i)z(i+1) squared by the variance. Weighted Cauchy-Schwarz then gives the stated estimate. All sums are finite, and no inverse operator or limiting argument is needed.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/BirthDeath." + name),
            H(title), TheoremStatement(name), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);

    private static StatementSource TheoremStatement(string name) =>
        name == "variance" ? StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), All("pi", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Equal(Call("variance", F.Id("n"), F.Id("pi"), F.Id("h")), SumRange("i", Add(F.Id("n"), Num(1)), Multiply(App(F.Id("pi"), F.Id("i")), new Formula.Power(Subtract(App(F.Id("h"), F.Id("i")), SumRange("j", Add(F.Id("n"), Num(1)), Multiply(App(F.Id("pi"), F.Id("j")), App(F.Id("h"), F.Id("j"))))), Num(2)))))))))) :
        name == "kappa" ? StatementSource.FromAuthor(Disp(All("p", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("r", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("i", F.Id("Nat"), Equal(Call("kappa", F.Id("p"), F.Id("r"), F.Id("i")), Subtract(Add(Subtract(App(F.Id("p"), F.Id("i")), App(F.Id("p"), Add(F.Id("i"), Num(1)))), App(F.Id("r"), Add(F.Id("i"), Num(1)))), App(F.Id("r"), F.Id("i"))))))))) :
        name == "variance_bound" ? StatementSource.FromAuthor(Disp(All("n", F.Id("Nat"), All("pi", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("p", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("r", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("h", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("n")), Lt(Num(0), App(F.Id("pi"), F.Id("i"))))), Implies(Equal(SumRange("i", Add(F.Id("n"), Num(1)), App(F.Id("pi"), F.Id("i"))), Num(1)), Implies(Equal(App(F.Id("p"), F.Id("n")), Num(0)), Implies(Equal(App(F.Id("r"), Num(0)), Num(0)), Implies(All("i", F.Id("Nat"), Implies(Lt(F.Id("i"), F.Id("n")), Lt(Num(0), App(F.Id("p"), F.Id("i"))))), Implies(All("i", F.Id("Nat"), Implies(Lt(Num(0), F.Id("i")), Implies(Le(F.Id("i"), F.Id("n")), Lt(Num(0), App(F.Id("r"), F.Id("i")))))), Implies(All("i", F.Id("Nat"), Implies(Lt(F.Id("i"), F.Id("n")), Equal(Multiply(App(F.Id("pi"), F.Id("i")), App(F.Id("p"), F.Id("i"))), Multiply(App(F.Id("pi"), Add(F.Id("i"), Num(1))), App(F.Id("r"), Add(F.Id("i"), Num(1))))))), Implies(All("i", F.Id("Nat"), Implies(Lt(F.Id("i"), F.Id("n")), Lt(Num(0), Call("kappa", F.Id("p"), F.Id("r"), F.Id("i"))))), Le(Call("variance", F.Id("n"), F.Id("pi"), F.Id("h")), SumRange("i", F.Id("n"), Multiply(new Formula.Fraction(Multiply(App(F.Id("pi"), F.Id("i")), App(F.Id("p"), F.Id("i"))), Call("kappa", F.Id("p"), F.Id("r"), F.Id("i"))), new Formula.Power(Subtract(App(F.Id("h"), Add(F.Id("i"), Num(1))), App(F.Id("h"), F.Id("i"))), Num(2)))))))))))))))))))) :
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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula SumRange(string name, Formula upper, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(F.Id(name), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), upper)), Sp, Parenthesized(body));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
}
