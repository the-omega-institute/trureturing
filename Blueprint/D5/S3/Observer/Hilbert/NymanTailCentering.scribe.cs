using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class NymanTailCenteringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/NymanTailCentering.";
    private static Formula N => F.Id("N");
    private static Formula C => F.Id("c");
    private static Formula One => D(1);
    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
    private static Formula App(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Sq(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula S => App(Sub("S", N), C);
    private static Formula U => App(Sub("U", N), C);
    private static Formula A => App(Sub("a", N), C);
    private static Formula G => App(Sub("g", N), C);
    private static Formula B => Sub("B", D(0));
    private static Formula R1 => Sub("r", One);
    private static Formula Whole => Sq(Norm(Seq(Chi, Minus, S)));
    private static Formula Local => Sq(Norm(Seq(One, Minus, U)));
    private static Formula CenteredError => Sq(Norm(Seq(One, Minus, G)));
    private static Formula Factor => Seq(Open, One, Plus, Sq(Norm(R1)), Close);
    private static Formula Bind => Seq(Forall, Sp, N, InMacro, Sp, Mathbb, Grp(F.Id("N")),
        Comma, Sp, Forall, Sp, C, InMacro, Sp, Mathbb, Grp(F.Id("C")),
        Caret, Grp(Operatorname, Grp(F.Id("Fin")), Open, N, Close), Comma, Sp);
    private static Formula InfDistance => App(Seq(Operatorname, Grp(F.Id("infDist"))),
        Seq(One, Comma, Overline, Grp(B)));

    private static DocumentBlock Theorem(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact tail energy and stable centering for finite Nyman approximants.",
        H("Nyman Tail Centering"), Blocks(
            Paragraph(Text("Use complex L2 with Lebesgue measure. On the positive half-line, chi is the indicator of (0,1) and rho_n(x) is fract(1/(n x)), for n at least one. On (0,1), r_n is the restriction of rho_n and the target is the constant one. The half-line and unit-interval norms below refer to these two distinct Hilbert spaces.")),
            Paragraph(Text("For every natural N, coefficients are indexed by n from one through N; equivalently n=i+1 for i in Fin N. Define S_N(c) as the sum of c_n rho_n and U_N(c) as the sum of c_n r_n. The empty sums are allowed. Define the tail coefficient and the corrected unit-interval approximant by")),
            Paragraph(Math(Disp(Seq(A, Eq, Sum, Underscore, Grp(F.Id("n"), Eq, One),
                Caret, Grp(N), Div(Sub("c", F.Id("n")), F.Id("n")), Comma, Sp,
                G, Eq, U, Minus, A, R1)))),
            Paragraph(Text("B_0 is the existing constrained Nyman class: finite sums of u_j fract(theta_j/x), where each real theta_j lies in (0,1] and the complex weighted coefficient sum of u_j theta_j is zero. Repeated parameters are permitted. Its closure and infimum distance use the unit-interval Hilbert norm. The number d_N is the distance from chi to the span of rho_1 through rho_N in the original positive-half-line Hilbert space.")),
            Theorem("finite_error_split", "The exact reciprocal-tail penalty",
                Seq(Bind, Whole, Eq, Local, Plus, Sq(Norm(A))),
                "For x greater than one, rho_n(x)=1/(n x), so the synthesis has tail a_N(c)/x. The integral of x to the power minus two on (1,infinity) is exactly one. Splitting the squared error at one gives the identity; the endpoint singleton has Lebesgue measure zero. No coefficient constraint is assumed."),
            Theorem("centered_approximation", "Explicit constrained approximation",
                Seq(Bind, G, InMacro, Sp, B, Land, Sp, CenteredError, Le, Factor, Whole),
                "Prepend coefficient minus a_N(c) at parameter one to the original unit-interval synthesis. The new weighted sum is exactly zero. The corrected error is the local error plus a_N(c) r_1. The triangle inequality and the nonnegative square of the difference between the local error norm times the norm of r_1 and the absolute tail coefficient give the stated bound. The factor is not asserted to be optimal on the arithmetic shells."),
            Theorem("constrained_distance_le", "Comparison with the finite Gram distance",
                Seq(Forall, Sp, N, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Sq(InfDistance), Le, Factor, Sq(Sub("d", N))),
                "The finite half-line span has an orthogonal projection of chi. Choose coefficients for that projection and apply the explicit centering estimate. Its corrected vector belongs to B_0 and hence to its closure, so the infimum distance is bounded by its error. The statement includes N=0 and assumes neither RH nor convergence of the finite distances."),
            Paragraph(Text("This comparison preserves the reciprocal tail when passing from half-line arithmetic approximation to the constrained unit-interval formulation. It supplies no new asymptotic approximation rate and does not construct the Volterra isometry used in the Burnol transformation."))
        ), [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hilbert/NymanHalflineMellinKernel")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hilbert/NymanUnitIntervalMellin"))
        ]));
}
