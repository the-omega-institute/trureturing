using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HwangKimTwoDimensionalCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact trace and determinant criterion for near order of positive two-dimensional matrices.",
        H("The exact two-dimensional criterion"),
        Blocks(Describe.Lean(DescribeId.Create("near-order-iff"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/HwangKimTwoDimensionalCriterion.near_order_iff"),
            H("Both directions, with the determinant condition"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/hwangkim2024nearorder")),
            Blocks(Paragraph(Text(
                "L and W are positive definite complex 2×2 matrices and det L=1. "
                + "Write d=√Re(det W), s=Re(tr W), t=Re(tr L), r=Re(tr(LW)) and "
                + "E=(s+dt)²−(1+d)²(r+2d). The determinant of W is a positive real number, "
                + "so d is its positive square root. The theorem is precisely "
                + "NearOrder L W iff 1≤d and E≤0. No transport equation or scalar sign bridge "
                + "is assumed in place of proving it for the actual mean.")),
                Paragraph(Text(
                "The actual positive transport C=L⁻¹#W satisfies CLC=W. The original "
                + "HwangKimNearOrderRefutation proof supplies det C=d and the two "
                + "Cayley–Hamilton trace identities through a shared private helper. "
                + "Positivity proves tr(LC)>0. The new sufficient direction uses the positive "
                + "eigenvalues c₁,c₂ of C: c₁c₂≥1 and c₁+c₂≤1+c₁c₂ force both to be at least one. "
                + "The determinant condition cannot be omitted. This is a criterion for arbitrary "
                + "positive L,W in dimension two with det L=1; it is not restricted to either witness.")),
                Paragraph(Text(
                "Source: the Ma–Zhang revision2 note, equation (criterion), "
                + "CC BY 4.0. Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: "
                + "NUS and ChronoAI, Singapore. The original Hwang–Kim question is the final "
                + "unnumbered display of arXiv:2407.07438v1 §6 p.17; equation (6.21) is a "
                + "different proved comparison. This formalization is not a priority claim. "
                + "Bhatia–Jain–Lim weak log-majorization and their norm/weak-majorization "
                + "Conjecture 1 are not refuted by this criterion."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Iff, P(y));
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, b);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sq(Formula x) => new Formula.Power(P(x), D(2));
    private static Formula Tr(Formula x) => C("Re", C("trace", x));
    private static Formula Mat => C("Matrix", C("Fin", D(2)), C("Fin", D(2)), Seq(Mathbb, Grp(V("C"))));

    private static Formula Statement()
    {
        Formula d = C("sqrt", C("Re", C("det", V("W"))));
        Formula e = Sub(Sq(Add(Tr(V("W")), Mul(d, Tr(V("L"))))),
            Mul(Sq(Add(D(1), d)), Add(Tr(Mul(V("L"), V("W"))), Mul(D(2), d))));
        return Disp(All("L", Mat, All("W", Mat,
            Imp(And(C("PosDef", V("L")), And(C("PosDef", V("W")), Eq(C("det", V("L")), D(1)))),
                Iff(C("NearOrder", V("L"), V("W")), And(Le(D(1), d), Le(e, D(0))))))));
    }
}
