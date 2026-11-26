using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class PositiveInteriorGridObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/PositiveInteriorGridObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reduced three by three spectral grid cannot have an interior product modulus.",
        H("Positive interior grid obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-interior-grid-algebraic-obstruction"),
                DeclarationHandle.Create(Module + ".positive_interior_grid_algebraic_obstruction"),
                H("The algebraic grid contradiction"),
                StatementSource.FromAuthor(Disp(StatementFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real and imaginary coordinates of two complex parameters satisfy the displayed sum and reduced second- and third-power equations. "
                        + "The variables s and t are their squared norms, and the final equation is the squared norm of their product. "
                        + "If the first imaginary coordinate is nonzero, the imaginary equation forces s and t to agree; the sum and norm equations then force the real coordinate to be one, making the product norm exceed one. "
                        + "If that imaginary coordinate is zero, both parameters are real and the reduced equation forces the product to have squared modulus one. "
                        + "Both cases contradict a product modulus strictly between zero and one.")),
                    Paragraph(Text(
                        "This result is the algebraic spectral-grid bridge. It assumes the reduced equations supplied by the preceding saturation argument; it does not assert the saturation lemma, the unitary spectral realization, or any conclusion at zero, endpoint, negative, or arbitrary-density parameters."))),
                DescribeRole.Theorem))));

    private static Formula StatementFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula r = F.Id("r");
        Formula ur = F.Id("ur");
        Formula ui = F.Id("ui");
        Formula vr = F.Id("vr");
        Formula vi = F.Id("vi");
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula Sum(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
        Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
        Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
        Formula Sq(Formula a) => new Formula.Power(a, D(2));
        Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
        Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
        Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
        Formula hypotheses = And(Lt(D(0), r), Lt(r, D(1)));
        hypotheses = And(hypotheses, Eq(Sum(ur, vr), D(2)));
        hypotheses = And(hypotheses, Eq(Sum(ui, vi), D(0)));
        Formula secondReal = Sum(Sum(Sum(Mul(ur, s), Mul(vr, t)), Mul(s, t)),
            Sub(D(3), Mul(D(3), Sum(s, t))));
        Formula secondImag = Sum(Mul(ui, s), Mul(vi, t));
        Formula productReal = Sub(Mul(ur, vr), Mul(ui, vi));
        Formula productImag = Sum(Mul(ur, vi), Mul(ui, vr));
        hypotheses = And(hypotheses, Eq(secondReal, D(0)));
        hypotheses = And(hypotheses, Eq(secondImag, D(0)));
        hypotheses = And(hypotheses, Eq(s, Sum(Sq(ur), Sq(ui))));
        hypotheses = And(hypotheses, Eq(t, Sum(Sq(vr), Sq(vi))));
        hypotheses = And(hypotheses, Eq(Sum(Sq(productReal), Sq(productImag)), Sq(r)));
        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("r"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("ur"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("ui"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("vr"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("vi"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("s"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("t"), real)
            ],
            new Formula.Logic(Parenthesized(hypotheses), FormulaLogicOperator.Implies, F.Id("False")));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
