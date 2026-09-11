using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class GribinskiDegreeThreeDiscriminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.";

    public DocumentDefinition Create()
    {
        Formula t = F.Id("t"), x = F.Id("x"), u = F.Id("u"), v = F.Id("v");
        Formula y = F.Id("y"), w = F.Id("w"), z = F.Id("z");
        Formula a1 = SumRoots(x, u, v), a2 = PairRoots(x, u, v), a3 = ProductRoots(x, u, v);
        Formula b1 = SumRoots(y, w, z), b2 = PairRoots(y, w, z), b3 = ProductRoots(y, w, z);
        Formula pairSum = Paren(Seq(a2, Plus, b2));
        Formula productSum = Paren(Seq(a3, Plus, b3));
        Formula numerator = new Formula.FunctionCall(FormulaIdentifier.Create("N"),
            [t, Seq(a1, Plus, b1),
                Seq(D(6), Cdot, pairSum, Plus, D(2), Cdot, Paren(a1), Cdot, Paren(b1)),
                Seq(D(3), Cdot, pairSum, Plus, D(2), Cdot, Paren(a1), Cdot, Paren(b1)),
                Seq(D(6), Cdot, productSum),
                Seq(D(3), Cdot, productSum, Plus, Paren(a1), Cdot, Paren(b2),
                    Plus, Paren(a2), Cdot, Paren(b1))]);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The denominator-cleared cubic discriminant is nonnegative for all "
                + "nonnegative ordered-gap coordinates and every nonnegative parameter t.",
            H("Degree-Three Gribinski Discriminant"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("discriminant-numerator"),
                    DeclarationHandle.Create(Prefix + "numerator"),
                    H("Denominator-Cleared Discriminant"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real t,s,a,b,c,d, N(t,s,a,b,c,d) denotes numerator t s a b c d. "
                            + "It is s^2*(a+b*t)^2*(6+3*t)-4*(a+b*t)^3 "
                            + "-4*s^3*(c+d*t)*(6+3*t)^2-27*(c+d*t)^2*(6+3*t) "
                            + "+18*s*(a+b*t)*(c+d*t)*(6+3*t)."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("ordered-numerator-nonnegative"),
                    DeclarationHandle.Create(Prefix + "ordered_numerator_nonneg"),
                    H("Nonnegativity on Ordered Gap Coordinates"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, t, Comma, x, Comma, u, Comma, v, Comma, y, Comma, w,
                        Comma, z, InMacro, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
                        Paren(Seq(Nonnegative(t), Sp, Land, Sp, Nonnegative(x), Sp, Land, Sp,
                            Nonnegative(u), Sp, Land, Sp, Nonnegative(v), Sp, Land, Sp,
                            Nonnegative(y), Sp, Land, Sp, Nonnegative(w), Sp, Land, Sp,
                            Nonnegative(z))), Sp, Implies, Sp, Nonnegative(numerator)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real t,x,u,v,y,w,z with 0<=t, 0<=x, 0<=u, 0<=v, "
                            + "0<=y, 0<=w and 0<=z, let A1=x+(x+u)+(x+u+v), "
                            + "A2=x*(x+u)+x*(x+u+v)+(x+u)*(x+u+v), "
                            + "A3=x*(x+u)*(x+u+v), B1=y+(y+w)+(y+w+z), "
                            + "B2=y*(y+w)+y*(y+w+z)+(y+w)*(y+w+z), "
                            + "and B3=y*(y+w)*(y+w+z). The conclusion is "
                            + "0<=N(t,A1+B1,6*(A2+B2)+2*A1*B1,3*(A2+B2)+2*A1*B1, "
                            + "6*(A3+B3),3*(A3+B3)+A1*B2+A2*B1). The displayed formula "
                            + "expands all six local definitions. The domain includes t=0 "
                            + "and zero gaps."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);
    private static Formula Nonnegative(Formula formula) => Seq(D(0), Le, Sp, formula);
    private static Formula SumRoots(Formula x, Formula u, Formula v) =>
        Seq(x, Plus, Paren(Seq(x, Plus, u)), Plus, Paren(Seq(x, Plus, u, Plus, v)));
    private static Formula PairRoots(Formula x, Formula u, Formula v) => Seq(
        x, Cdot, Paren(Seq(x, Plus, u)), Plus,
        x, Cdot, Paren(Seq(x, Plus, u, Plus, v)), Plus,
        Paren(Seq(x, Plus, u)), Cdot, Paren(Seq(x, Plus, u, Plus, v)));
    private static Formula ProductRoots(Formula x, Formula u, Formula v) =>
        Seq(x, Cdot, Paren(Seq(x, Plus, u)), Cdot, Paren(Seq(x, Plus, u, Plus, v)));
}
