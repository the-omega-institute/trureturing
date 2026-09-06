using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CoefficientMultiplicationTraceMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient multiplication power traces recover root moments with algebraic multiplicity.",
        H("Coefficient Multiplication Trace Moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("coefficient-multiplication-trace-pow-eq-root-power-moment"),
            DeclarationHandle.Create(
                "D5/S3/Constants/Moments/CoefficientMultiplicationTraceMoments."
                    + "coefficient_multiplication_trace_pow_eq_rootPowerMoment"),
            H("Every normalized power trace is the corresponding root moment"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be a real polynomial of positive degree d, with a specified "
                        + "factorization into d monic linear factors over the complex numbers. "
                        + "The indexed factors retain algebraic multiplicity. This factorization "
                        + "already forces q to be monic. For every natural exponent, including "
                        + "zero, the real trace of the coefficient multiplication matrix power, "
                        + "divided by d, equals rootPowerMoment for that root list.")),
                Paragraph(Text(
                    "Put the roots on the diagonal of a lower bidiagonal matrix T and put "
                        + "ones on its subdiagonal. The Krylov columns T^j e_0 form an upper "
                        + "triangular matrix P with diagonal one. Its determinant is therefore "
                        + "one even when roots repeat or vanish. Cayley-Hamilton supplies the "
                        + "last column of the intertwining identity P S = T P, where S is "
                        + "the complex image of the real coefficient multiplication matrix.")),
                Paragraph(Text(
                    "The intertwining identity extends to every power. Invariance of trace "
                        + "under conjugation reduces the trace to T, whose power has diagonal "
                        + "entries equal to the corresponding root powers. Taking real parts "
                        + "and dividing by d connects the coefficient matrix definition to "
                        + "the root moment definition. Distinctness, real roots, positivity "
                        + "and nonzero roots are not required."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula d = Call("natDegree", q);
        Formula roots = F.Id("roots");
        Formula j = F.Id("j");
        Formula n = F.Id("n");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula root = new Formula.Apply(roots, [j]);
        Formula matrix = Call("coefficientMultiplicationMatrix", q);
        Formula powerTrace = Call("tr", Seq(matrix, Caret, Grp(n)));
        Formula factorization = Seq(
            Call("map", F.Id("ofRealHom"), q), Sp, Eq, Sp,
            Prod, Underscore, Grp(j, Sp, InMacro, Sp, Call("Fin", d)), Sp,
            Open, F.Id("X"), Sp, Minus, Sp, Call("C", root), Close);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, q, Colon, Sp, Call("Polynomial", reals), Comma, Sp,
                roots, Colon, Sp, Call("Fin", d), Sp, To, Sp, complexes, Comma),
            Seq(D(0), Sp, Lt, Sp, d, Sp, Land, Sp, factorization, Sp, Rightarrow),
            Seq(Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
                Frac, Grp(powerTrace), Grp(d), Sp, Eq, Sp,
                Call("rootPowerMoment", roots, n), Dot),
        ]));
    }
}
