using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class WeightingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite one-sign-change weighting for the gamma-series transformation.",
        H("Increasing weights"), Blocks(
            Entry("karp-zhang-gamma-weighted-sum", "weighted_sum_nonneg", "Finite weighting principle",
                "Let A and W be real sequences and h a natural number. Assume that for all i,j <= h with i < j, A(i) > 0 implies A(j) >= 0; that the sum of A(i) for 0 <= i <= h is nonnegative; that W(i) >= 0 for i <= h; and that W(i) <= W(j) for i <= j <= h. Then the sum of A(i)W(i) for 0 <= i <= h is nonnegative. Zero entries and either empty sign group are allowed."),
            Entry("karp-zhang-gamma-coefficientwise-weighting", "coefficientwise_weighting", "Coefficientwise weighting principle",
                "Let A be a real sequence, W a function from two natural indices to the reals, and h a natural number. Assume the same scalar sign condition and total-sum condition as in weighted_sum_nonneg. Assume for every natural degree N that W(i,N) is nonnegative for i <= h and W(i,N) <= W(j,N) for i <= j <= h. For every natural N the sum of A(i)W(i,N) over i=0,...,h is nonnegative."),
            Paragraph(Text("Choose the least positive term of A. Every earlier term is nonpositive and every later term is nonnegative. Subtracting the weight at that index makes each product nonnegative, while the residual constant weight multiplies the nonnegative total sum. If no positive term exists, the total-sum condition forces all terms to vanish. Applying this argument independently in each degree proves the coefficientwise statement without convergence or division of formal series.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Weighting." + name),
            H(title), TheoremStatement(name), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static StatementSource TheoremStatement(string name) =>
        name == "weighted_sum_nonneg" ? StatementSource.FromAuthor(Disp(All("A", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("W", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("h", F.Id("Nat"), Implies(All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("h")), All("j", F.Id("Nat"), Implies(Le(F.Id("j"), F.Id("h")), Implies(Lt(F.Id("i"), F.Id("j")), Implies(Lt(Num(0), App(F.Id("A"), F.Id("i"))), Le(Num(0), App(F.Id("A"), F.Id("j"))))))))), Implies(Le(Num(0), SumRange("i", Add(F.Id("h"), Num(1)), App(F.Id("A"), F.Id("i")))), Implies(All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("h")), Le(Num(0), App(F.Id("W"), F.Id("i"))))), Implies(All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("h")), All("j", F.Id("Nat"), Implies(Le(F.Id("j"), F.Id("h")), Implies(Le(F.Id("i"), F.Id("j")), Le(App(F.Id("W"), F.Id("i")), App(F.Id("W"), F.Id("j")))))))), Le(Num(0), SumRange("i", Add(F.Id("h"), Num(1)), Multiply(App(F.Id("A"), F.Id("i")), App(F.Id("W"), F.Id("i")))))))))))))) :
        name == "coefficientwise_weighting" ? StatementSource.FromAuthor(Disp(All("A", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("W", new Formula.TypeArrow(F.Id("Nat"), new Formula.TypeArrow(F.Id("Nat"), F.Id("Real"))), All("h", F.Id("Nat"), Implies(All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("h")), All("j", F.Id("Nat"), Implies(Le(F.Id("j"), F.Id("h")), Implies(Lt(F.Id("i"), F.Id("j")), Implies(Lt(Num(0), App(F.Id("A"), F.Id("i"))), Le(Num(0), App(F.Id("A"), F.Id("j"))))))))), Implies(Le(Num(0), SumRange("i", Add(F.Id("h"), Num(1)), App(F.Id("A"), F.Id("i")))), Implies(All("N", F.Id("Nat"), All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("h")), Le(Num(0), App(F.Id("W"), F.Id("i"), F.Id("N")))))), Implies(All("N", F.Id("Nat"), All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("h")), All("j", F.Id("Nat"), Implies(Le(F.Id("j"), F.Id("h")), Implies(Le(F.Id("i"), F.Id("j")), Le(App(F.Id("W"), F.Id("i"), F.Id("N")), App(F.Id("W"), F.Id("j"), F.Id("N"))))))))), All("N", F.Id("Nat"), Le(Num(0), SumRange("i", Add(F.Id("h"), Num(1)), Multiply(App(F.Id("A"), F.Id("i")), App(F.Id("W"), F.Id("i"), F.Id("N"))))))))))))))) :
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
