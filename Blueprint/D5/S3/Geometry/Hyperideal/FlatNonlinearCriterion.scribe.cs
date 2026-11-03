using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FlatNonlinearCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Hyperideal/FlatNonlinearCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact nonlinear correction separates the flat boundary from the symmetric transverse case.",
        H("Exact nonlinear flat criterion"),
        Blocks(
            Paragraph(Text("Use the six independent positive coordinates in the order (r,a,b,o,c,d). Set A=rad(r,a,d), B=rad(r,b,c), C=r^2-1+(a-d)(c-b)+2(r+1)sqrt(abcd), S=sqrt(ac)+sqrt(bd), and J=(sqrt(AB)-C)/(r+1). The auxiliary C is the inner product of the two explicit three-dimensional vectors used in the Cauchy bound.")),
            Paragraph(Text("The correction J is nonnegative. The original cosine is at most -1 exactly when the opposite product (r-1)(o-1) reaches S^2+J. Equality J=0 occurs exactly on the opposite-pair symmetry a=c and b=d; there the criterion reduces to (r-1)(o-1)>=(a+b)^2.")),
            Node("j-nonneg", "Nonnegative nonlinear correction", "J_nonneg", JNonneg(), "Finite Cauchy-Schwarz applied to the explicit three-coordinate vectors proves C<=sqrt(AB), and the positive factor r+1 preserves the inequality."),
            Node("exact-flat-criterion", "Exact flat iff", "cosine_le_neg_one_iff", ExactCriterion(), "Expanding numerator+C gives (r+1)(S^2-(r-1)(o-1)); replacing sqrt(AB) by C+(r+1)J and using the positive denominator yields the iff."),
            Node("j-equality", "Equality characterization", "J_eq_zero_iff", Equality(), "The Gram determinant is a sum of three squares. Its vanishing forces equality of the two vector coordinates and then a=c and b=d; the converse follows by direct substitution."),
            Node("symmetric-flat-criterion", "Symmetric transverse reduction", "symmetric_cosine_le_neg_one_iff", Symmetric(), "When c=a and d=b, the square-root terms reduce to a and b and the equality characterization gives J=0, yielding the sharp reduced product test."))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula JNonneg()
    {
        var v = new[] { "r", "a", "b", "c", "d" };
        var x = v.Select(F.Id).ToArray();
        return All(v, Imp(And(v.Select(n => Lt(F.D(1), F.Id(n))).ToArray()),
            Le(F.D(0), Call("J", x))));
    }

    private static Formula ExactCriterion()
    {
        var v = new[] { "r", "a", "b", "o", "c", "d" };
        var x = v.Select(F.Id).ToArray();
        var pos = And(v.Select(n => Lt(F.D(1), F.Id(n))).ToArray());
        var lhs = Le(Call("cosine", x), Neg(F.D(1)));
        var rhs = Ge(Mul(Sub(x[0], F.D(1)), Sub(x[3], F.D(1))),
            Add(Pow(Call("S", x[1], x[2], x[4], x[5]), 2), Call("J", x[0], x[1], x[2], x[4], x[5])));
        return All(v, Imp(pos, Iff(lhs, rhs)));
    }

    private static Formula Equality()
    {
        var v = new[] { "r", "a", "b", "c", "d" };
        var x = v.Select(F.Id).ToArray();
        var pos = And(v.Select(n => Lt(F.D(1), F.Id(n))).ToArray());
        return All(v, Imp(pos, Iff(Eq(Call("J", x), F.D(0)), And(Eq(x[1], x[3]), Eq(x[2], x[4])))));
    }

    private static Formula Symmetric()
    {
        var v = new[] { "r", "a", "b", "o" };
        var x = v.Select(F.Id).ToArray();
        var pos = And(v.Select(n => Lt(F.D(1), F.Id(n))).ToArray());
        var lhs = Le(Call("cosine", x[0], x[1], x[2], x[3], x[1], x[2]), Neg(F.D(1)));
        var rhs = Ge(Mul(Sub(x[0], F.D(1)), Sub(x[3], F.D(1))), Pow(Add(x[1], x[2]), 2));
        return All(v, Imp(pos, Iff(lhs, rhs)));
    }

    private static Formula All(string[] names, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(n => new Formula.BoundVariable(FormulaIdentifier.Create(n), F.Id("Real")))], body);

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ge(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.GreaterThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, int n) => new Formula.Power(a, F.D((byte)n));
    private static Formula Neg(Formula a) => new Formula.Negate(a);
}
