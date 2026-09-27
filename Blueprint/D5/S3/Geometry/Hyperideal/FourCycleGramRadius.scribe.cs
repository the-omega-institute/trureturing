using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleGramRadiusDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleGramRadius.gram_det_radius";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative Gram determinant criterion for six independent cosine lengths.",
        H("Six-length Gram radius"),
        Blocks(
            Paragraph(Text("Use the edge order (12,13,14,34,24,23) and the signed "
                + "4-by-4 matrix gram(r,a,b,o,c,d) from the Lean source. Set "
                + "A=(a+c)/2, B=(b+d)/2, xi=(a-c)/2, zeta=(b-d)/2, "
                + "L=(A+B)^2-(r-1)(o-1), M=(r+1)(o+1)-(A-B)^2, "
                + "t=xi^2+zeta^2, and "
                + "C=ro-1+sqrt((A^2-B^2)^2+(r-o)^2).")),
            Describe.Lean(
                DescribeId.Create("six-length-fourcycle-gram-radius"),
                DeclarationHandle.Create(Declaration),
                H("The quantitative radius makes the signed Gram determinant negative"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For six independent cosine lengths greater than one, "
                        + "positive L and M, and t^2+2Ct<LM, the signed Gram "
                        + "determinant is strictly negative.")),
                    Paragraph(Text("The determinant expands as -LM plus an anisotropic "
                        + "quadratic and a quartic term. A two-dimensional Cauchy "
                        + "bound controls the quadratic term by 2Ct; the quartic "
                        + "term is at most t^2.")),
                    Paragraph(Text("This is a statement about the six-variable "
                        + "matrix. It does not construct a hyperideal tetrahedron, "
                        + "prove a cosine-range equivalence, or establish a global "
                        + "CFMP realization."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = F.Id("r"); var a = F.Id("a"); var b = F.Id("b");
        var o = F.Id("o"); var c = F.Id("c"); var d = F.Id("d");
        var one = F.D(1); var two = F.D(2);
        var aMean = Div(Add(a, c), two);
        var bMean = Div(Add(b, d), two);
        var xi = Div(Sub(a, c), two);
        var zeta = Div(Sub(b, d), two);
        var l = Sub(Pow(Add(aMean, bMean)), Mul(Sub(r, one), Sub(o, one)));
        var m = Sub(Mul(Add(r, one), Add(o, one)), Pow(Sub(aMean, bMean)));
        var t = Add(Pow(xi), Pow(zeta));
        var radiusCoefficient = Add(Sub(Mul(r, o), one),
            Call("sqrt", Add(Pow(Sub(Pow(aMean), Pow(bMean))), Pow(Sub(r, o)))));
        var premise = And(
            Lt(one, r), Lt(one, a), Lt(one, b),
            Lt(one, o), Lt(one, c), Lt(one, d),
            Lt(F.D(0), l), Lt(F.D(0), m),
            Lt(Add(Pow(t), Mul(two, radiusCoefficient, t)), Mul(l, m)));
        var conclusion = Lt(Call("det", Call("gram", r, a, b, o, c, d)), F.D(0));
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = [.. new[] { "r", "a", "b", "o", "c", "d" }
            .Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), real))];
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction.");
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(params Formula[] terms)
    {
        if (terms.Length == 0) throw new ArgumentException("Empty product.");
        var result = terms[0];
        for (var i = 1; i < terms.Length; i++)
            result = new Formula.Binary(result, FormulaBinaryOperator.Multiply, terms[i]);
        return result;
    }
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Pow(Formula value) => new Formula.Power(value, F.D(2));
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
