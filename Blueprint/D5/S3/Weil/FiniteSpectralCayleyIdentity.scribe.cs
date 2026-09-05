using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class FiniteSpectralCayleyIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/FiniteSpectralCayleyIdentity."
            + "finiteLiCoefficient_eq_diagonalHilbertSchmidtDefect";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite real spectrum obeys the Li-Cayley norm identity and its diagonal "
            + "determinant product.",
        H("Finite Spectral Cayley Identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-li-coefficient-is-a-diagonal-hilbert-schmidt-defect"),
            DeclarationHandle.Create(Declaration),
            H("The finite Li coefficient is a diagonal Hilbert-Schmidt defect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be a finite index type and let gamma assign a real spectral "
                        + "ordinate to every index. Put x(t)=1/(4t^2+1) and "
                        + "C(t)=1-2x(t)+2i sqrt(x(t)(1-x(t))). The denominator is positive, "
                        + "x(t) lies in (0,1], and the square-root radicand is nonnegative.")),
                Paragraph(Text(
                    "Each C(t) has squared norm one. Expanding the squared norm of "
                        + "1-C(t)^n and using that complex conjugation preserves real parts "
                        + "gives the displayed identity term by term, hence after summing "
                        + "over J.")),
                Paragraph(Text(
                    "The same Lean module proves the first-power identity "
                        + "sum |1-C(gamma_j)|^2 = 4 sum x(gamma_j), and evaluates the "
                        + "determinant of the corresponding finite diagonal matrix as the "
                        + "product of its scalar spectral factors.")),
                Paragraph(Text(
                    "This corrects the source claim to the algebra justified by the stated "
                        + "data. No automorphic L-function, GRH implication, infinite "
                        + "Hilbert-Schmidt operator, or Fredholm determinant is asserted; "
                        + "those require analytic and operator-theoretic infrastructure not "
                        + "present in the formal statement."))),
            DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula FiniteSum(Formula index, Formula carrier, Formula body) =>
        Seq(Sum, Underscore, Grp(index, Sp, InMacro, Sp, carrier), Sp, body);

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("J");
        Formula gamma = GammaLower;
        Formula j = F.Id("j");
        Formula n = F.Id("n");
        Formula nodePower = Seq(
            Call("C", Indexed(gamma, j)), Caret, Grp(n));
        Formula liTerm = Seq(
            D(2), Open, D(1), Sp, Minus, Sp, Re, Open, nodePower, Close, Close);
        Formula defectTerm = Seq(
            new Formula.Absolute(Seq(D(1), Sp, Minus, Sp, nodePower)), Caret, Grp(D(2)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, carrier, Sp, Mathrm, Grp(F.Id("finite")), Comma, Sp,
                gamma, Colon, Sp, carrier, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma),
            Seq(
                FiniteSum(j, carrier, liTerm), Sp, Eq, Sp,
                FiniteSum(j, carrier, defectTerm), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
