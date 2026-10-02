using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class FiniteBoxDeterminantTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary logarithm of a finite determinant product records common-divisor power traces.",
        H("Finite Box Determinant Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-box-determinant-trace"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Dilation/FiniteBoxDeterminantTrace.finite_box_trace_formula"),
                H("Common-divisor traces of actual actions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be a group and let W(m,n) be finite-dimensional rational "
                            + "G-representations. Only positive bidegrees occur in the finite "
                            + "box. The group may in particular be finite. Dimensions can vary "
                            + "with the bidegree and can be zero. The action matrix is the "
                            + "matrix of the given representation in a finite basis.")),
                    Paragraph(Text(
                        "D(g,N) is the literal product of det(I-p^m q^n rho(m,n)(g)) "
                            + "for 1 <= m,n <= N. Each matrix determinant equals the intrinsic "
                            + "determinant of I-p^m q^n times the action after extension of "
                            + "scalars to the bivariate rational series ring. Thus the product "
                            + "is independent of the finite bases. Its constant coefficient "
                            + "is one. The negative logarithm is the ordinary formal series "
                            + "log(1+X) substituted at D(g,N)-1 and negated.")),
                    Paragraph(Text(
                        "For a rational matrix A, its formal resolvent has coefficient A^k "
                            + "in degree k. The first-order Taylor determinant identity applied "
                            + "at I-XA gives its logarithmic derivative. Integration with zero "
                            + "constant term yields trace(A^k)/k as every positive coefficient "
                            + "of -log det(I-XA). This uses no diagonalization and also applies "
                            + "to the empty matrix.")),
                    Paragraph(Text(
                        "Writing the bivariate ring as iterated series preserves ordinary "
                            + "logarithm substitution. Over the inner coefficient ring, the "
                            + "logarithmic derivative proves that the logarithm of a finite "
                            + "product is the sum of the factor logarithms. Substitution of "
                            + "p^m q^n leaves precisely exponents (km,kn). Reindexing these "
                            + "contributions by divisors of gcd(a,b) gives the displayed "
                            + "formula. Every required quotient bidegree lies in each box "
                            + "with N >= max(a,b), proving stability.")),
                    Paragraph(Text(
                        "This is a finite-dimensional algebraic identity for the supplied "
                            + "actions. It constructs no infinite product and asserts no "
                            + "Monster root-space, vertex-algebra, or conformal-field structure."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), k = F.Id("k");
        Formula m = F.Id("m"), n = F.Id("n"), g = F.Id("g");
        Formula N = F.Id("N"), M = F.Id("M"), p = F.Id("p"), q = F.Id("q");
        Formula D(Formula box) => new Formula.Subscript(F.Id("D"), F.Seq(g, F.Comma, box));
        Formula Rho(Formula x, Formula y, Formula h) => F.Seq(
            new Formula.Subscript(F.Rho, F.Seq(x, F.Comma, y)), F.Open, h, F.Close);
        Formula Tr(Formula x) => F.Seq(F.Operatorname, F.Grp(F.Id("tr")), F.Open, x, F.Close);
        Formula Det(Formula x) => F.Seq(F.Operatorname, F.Grp(F.Id("det")), F.Open, x, F.Close);
        Formula Coeff(Formula box) => F.Seq(F.OpenBracket, Pow(p, a), Pow(q, b), F.CloseBracket,
            F.Open, F.Minus, F.Log, F.Sp, D(box), F.Close);
        Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
        Formula sum = F.Seq(F.Sum, F.Underscore,
            F.Grp(k, F.Mid, Call("gcd", a, b)), F.Sp,
            new Formula.Fraction(Tr(Rho(new Formula.Fraction(a, k),
                new Formula.Fraction(b, k), Pow(g, k))), k));
        Formula product = F.Seq(F.Prod, F.Underscore,
            F.Grp(F.D(1), F.Le, F.Sp, m, F.Comma, n, F.Le, F.Sp, N), F.Sp,
            Det(F.Seq(F.Id("I"), F.Minus, Pow(p, m), Pow(q, n), Rho(m, n, g))));
        Formula condition = F.Seq(a, F.Comma, b, F.Ge, F.D(1), F.Comma, F.Sp,
            N, F.Ge, Call("max", a, b));
        Formula formula = F.Seq(F.Forall, F.Sp, a, F.Comma, b, F.Comma, N, F.Comma, F.Sp,
            condition, F.Sp, F.Implies, F.Sp, Eq(Coeff(N), sum));
        Formula stability = F.Seq(F.Forall, F.Sp, a, F.Comma, b, F.Comma,
            N, F.Comma, M, F.Comma, F.Sp,
            a, F.Comma, b, F.Ge, F.D(1), F.Comma, F.Sp,
            N, F.Comma, M, F.Ge, Call("max", a, b), F.Sp, F.Implies, F.Sp,
            Eq(Coeff(N), Coeff(M)));
        return F.Disp(new Formula.Aligned([
            Eq(D(N), product),
            formula,
            stability,
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.Add(F.Comma);
            pieces.Add(arguments[i]);
        }
        pieces.Add(F.Close);
        return F.Seq([.. pieces]);
    }

    private static Formula Pow(Formula value, Formula degree) => F.Seq(value, F.Caret, F.Grp(degree));
}
