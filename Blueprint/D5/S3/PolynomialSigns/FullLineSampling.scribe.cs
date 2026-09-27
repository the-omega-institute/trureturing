using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PolynomialSigns;

internal sealed class FullLineSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PolynomialSigns/FullLineSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every jointly realized sign vector of a finite real polynomial family occurs "
            + "on one tail, at a common product root, or at a common critical point.",
        H("Joint signs on the real line"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("polynomial-sign-code"),
                DeclarationHandle.Create(Prefix + "ternary"),
                H("Three sign codes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real a, ternary(a) is 0 when a < 0, "
                    + "1 when a = 0, and 2 when a > 0. Its codomain is Fin 3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-line-joint-sign-sampling"),
                DeclarationHandle.Create(Prefix + "full_line_sampling"),
                H("One representative for the entire sign vector"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural m, every family f indexed by Fin m "
                        + "of real univariate polynomials, and every s from Fin m to Fin 3, "
                        + "put P(f) equal to the product over all i of 1 if f(i) is the zero "
                        + "polynomial, and f(i) otherwise. Roots(q) means the finite support "
                        + "q.roots.toFinset. In the formula, signs(f,y) means that for every "
                        + "i in Fin m, ternary(f(i).eval(y)) = s(i). PositiveTail(f,s) means "
                        + "that for every i, ternary(f(i).leadingCoeff) = s(i). "
                        + "NegativeTail(f,s) instead uses the leading coefficient of "
                        + "f(i) composed with -X.")),
                    Paragraph(Text("The same real y realizes every prescribed sign. Each "
                        + "root alternative also uses one common r for all members; "
                        + "individually attainable signs are insufficient. If y is not a "
                        + "product root, the nearest product roots bound a root-free interval, "
                        + "or y lies in an outer cell. Rolle's theorem supplies a critical "
                        + "point in each bounded interval. The intermediate value theorem "
                        + "keeps every nonzero member's sign fixed throughout that interval. "
                        + "On an outer cell the finite family has simultaneous eventual "
                        + "signs determined by the corresponding leading coefficients.")),
                    Paragraph(Text("No nonzero, positive-degree, squarefree or coprime "
                        + "hypothesis is imposed on the family. Empty families, zero "
                        + "polynomials, constants and repeated roots are included. P(f) is "
                        + "always nonzero. When its derivative is zero, the derivative root "
                        + "support is empty; it does not represent every real zero of the "
                        + "zero polynomial. The result is a universal sampling "
                        + "characterization over arbitrary real coefficients. It gives no "
                        + "effective executable procedure or complexity bound."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Statement()
    {
        var m = F.Id("m"); var f = F.Id("f"); var s = F.Id("s");
        var p = Call("P", f);
        Formula Signs(Formula y) => All("i", Call("Fin", m),
            new Formula.Relation(Call("ternary", Call("eval", Call("f", F.Id("i")), y)),
                FormulaRelationOperator.Equal, Call("s", F.Id("i"))));
        var productRoot = Exists("r", Call("Roots", p), Signs(F.Id("r")));
        var criticalRoot = Exists("r", Call("Roots", Call("derivative", p)), Signs(F.Id("r")));
        var alternatives = Or(Call("PositiveTail", f, s),
            Or(Call("NegativeTail", f, s), Or(productRoot, criticalRoot)));
        var equivalence = new Formula.Logic(
            Exists("y", F.Id("Real"), Signs(F.Id("y"))),
            FormulaLogicOperator.Iff, alternatives);
        return F.Disp(All("m", F.Id("Nat"),
            All("f", new Formula.TypeArrow(Call("Fin", m), Call("Polynomial", F.Id("Real"))),
                All("s", new Formula.TypeArrow(Call("Fin", m), Call("Fin", F.D(3))), equivalence))));
    }
}
