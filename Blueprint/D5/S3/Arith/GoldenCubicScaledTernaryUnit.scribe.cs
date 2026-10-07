using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenCubicScaledTernaryUnitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native ternary Lucas layers have exact three-adic valuations and alternating scaled units.",
        H("Native Scaled Ternary Lucas Units"),
        Blocks(
            Paragraph(Text(
                "Let phi be the golden integer with phi squared equal to phi plus one. "
                + "The integer L_n is goldenLucas n, the trace of phi^n. "
                + "For every natural j, put A_j=L_(3^j)^2+2. The symbol v_3 denotes "
                + "padicValInt 3 on these positive integers. Powers have natural exponents.")),
            new DocumentBlock.DisplayFormula(Seq(
                F.Id("L"), Underscore, F.Id("n"), Eq,
                Operatorname, Grp(F.Id("Tr")), Open, Varphi, Caret, F.Id("n"), Close,
                Comma, Quad, Sp,
                Layer(), Eq, F.Id("L"), Underscore, Grp(Power(D(3), F.Id("j"))),
                Caret, D(2), Plus, D(2))),
            Describe.Lean(
                DescribeId.Create("native-scaled-ternary-unit"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/GoldenCubicScaledTernaryUnit.golden_cubic_scaled_ternary_unit"),
                H("Exact depth and signed integer quotient"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural j at least one, A_j has three-adic valuation j+1. "
                        + "The displayed fraction is exact integer division in Z: "
                        + "3^(j+1) divides A_j, and the resulting integer has residue (-1)^j "
                        + "modulo three.")),
                    Paragraph(Text(
                        "The native cubic Lucas identity gives A_(k+1)=A_k(A_k^2-3), "
                        + "starting from A_0=3. Induction constructs an integer u_k with "
                        + "A_k=3^(k+1)u_k and u_k congruent to (-1)^k modulo three. "
                        + "The successor is u_(k+1)=u_k(3(3^k)^2u_k^2-1), so its residue "
                        + "is the negative of the preceding residue. Exact division by the "
                        + "positive power 3^(j+1) recovers this same u_j.")),
                    Paragraph(Text(
                        "For the valuation, Fibonacci and Lucas doubling give "
                        + "F_(4*3^j)=F_(3^j)L_(3^j)A_j. The first two factors are nonzero "
                        + "and indivisible by three. The Fibonacci valuation at index "
                        + "4*3^j is j+1, hence the valuation of A_j is j+1 as well."))),
                DescribeRole.Theorem))));

    private static Formula Layer() => new Formula.Subscript(F.Id("A"), F.Id("j"));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula ResultFormula()
    {
        Formula j = F.Id("j");
        Formula next = new Formula.Binary(j, FormulaBinaryOperator.Add, D(1));
        Formula valuation = new Formula.Apply(
            new Formula.Subscript(F.Id("v"), D(3)), [Layer()]);
        Formula depth = new Formula.Relation(valuation, FormulaRelationOperator.Equal, next);
        Formula quotient = Seq(Frac, Grp(Layer()), Grp(Power(D(3), next)));
        Formula signedUnit = Seq(quotient, Sp, Equiv, Sp,
            Power(Parenthesized(Seq(Minus, D(1))), j), Sp,
            Open, Operatorname, Grp(F.Id("mod")), Sp, D(3), Close);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("j"), Seq(Mathbb, Grp(F.Id("N"))))],
            new Formula.Logic(
                Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, j)),
                FormulaLogicOperator.Implies,
                Parenthesized(new Formula.Logic(
                    Parenthesized(depth), FormulaLogicOperator.And, Parenthesized(signedUnit))))));
    }
}
