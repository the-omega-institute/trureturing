using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class SchurIntegratedKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Interpolation/SchurIntegratedKernel.";
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Functions => Seq(C, Sp, To, Sp, C);
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula B => F.Id("b");
    private static Formula X => F.Id("x");
    private static Formula T => F.Id("t");
    private static Formula Q => F.Id("theta");
    private static Formula P => Call("poissonDensity", T, Q);
    private static Formula A => Call("integratedPoisson", X, Q);
    private static Formula All(string v, Formula body) =>
        Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, R, Comma, Sp, body);
    private static Formula Eqn(Formula l, Formula r) => Seq(l, Sp, Eq, Sp, r);
    private static Formula Integral(string v, Formula lo, Formula hi, Formula body) =>
        Call("integral", lo, hi, Seq(Open, F.Id(v), Sp, Colon, Sp, R, Close, Sp, Mapsto, Sp, body));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Poisson densities and the Fourier boundary kernel satisfy normalized L1 control on the strict interior real interval, including the closed parameter edge b=1.",
        H("The integrated Poisson and signed Schur kernel"), Blocks(
            Entry("density", "poissonDensity", "The actual disk Poisson density",
                Disp(All("t", All("theta", Eqn(P,
                    Call("poissonKernel", D(0), T, Call("circleMap", D(0), D(1), Q)))))),
                "The function uses Mathlib's actual disk Poisson kernel at the real point t and actual unit-circle point circleMap(0,1,theta). The kernel is used only for |t|<1; no boundary Poisson formula is assumed.", DescribeRole.Definition),
            Entry("integrated", "integratedPoisson", "The oriented Poisson integral",
                Disp(All("x", All("theta", Eqn(A, Integral("t", D(0), X, P))))),
                "The interval integral runs from zero to x with its orientation. For |x|<1, the entire segment lies strictly inside the disk. The angle function is continuous and all integrals used in the proof exist.", DescribeRole.Definition),
            Entry("l1", "boundary_l1_control", "Normalized L1 control on the entire interior interval",
                Disp(All("b", All("x", Seq(D(0), Sp, Le, Sp, B, Sp, Le, Sp, D(1), Sp, Land, Sp,
                    Call("abs", X), Sp, Lt, Sp, D(1), Sp, Implies, Sp,
                    Frac, Grp(D(1)), Grp(D(2), Pi), Sp,
                    Integral("theta", D(0), Seq(D(2), Pi),
                        Call("abs", Seq(A, Minus, Call("boundaryKernel", B, Q)))),
                    Sp, Le, Sp, D(1))))),
                "The normalized integral of |A_x-B_b| is at most one for every |x|<1 and b in [0,1]. On nonnegative x, the Poisson lower estimate and the polynomial sum from k=1 to 5 of ((1-t)/2)^k yield A_x >= x(367/960) >= x(3067/8100). The polynomial's integral is exactly 367/960. The actual Poisson mean is one, proved by applying the Poisson formula to the constant complex function; continuous integrability on the compact time-angle rectangle justifies the swap giving mean A_x=x. The boundary kernel has mean zero and absolute value at most 3067/8100. Therefore |A_x-B_b| <= A_x-B_b+2(1-x)(3067/8100), and its mean is at most one. The identities P(-t,theta)=P(t,theta+pi) and B_b(theta+pi)=-B_b(theta), with periodic interval integration, prove the negative-x case. The value b=1 uses the proved closed-domain kernel controls. This scalar control bounds the actual primitive functional below, using its derived boundary representation.", DescribeRole.Theorem),
            Entry("primitive-bound", "primitive_error_bound", "The sharp actual primitive functional on the closed interval",
                Disp(All("b", All("x", Seq(
                    Forall, Sp, F.Id("h"), Sp, F.Id("H"), Sp, Colon, Sp, Functions, Comma, Sp,
                    Call("Entire", F.Id("h")), Sp, Land, Sp,
                    Call("HasDerivativeEverywhere", F.Id("H"), F.Id("h")), Sp, Land, Sp,
                    Eqn(Call("H", D(0)), D(0)), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, B, Sp, Le, Sp, D(1), Sp, Land, Sp,
                    Seq(Minus, D(1)), Sp, Le, Sp, X, Sp, Le, Sp, D(1), Sp, Implies, Sp,
                    Call("norm", Seq(Call("H", X), Minus,
                        Frac, Grp(D(1)), Grp(D(2), B),
                        Integral("t", Seq(Minus, B), B, Call("H", Seq(T, F.Id("i")))))),
                    Sp, Le, Sp, Call("sSup", Call("normImageOfClosedDisk", F.Id("h"))))))),
                "Let h be any entire complex-valued function and H its normalized entire primitive. For every 0<b<=1 and every real x in [-1,1], the norm of H(x) minus its normalized imaginary-segment average is at most the supremum of |h| on the original closed unit disk. The norm value set is nonempty and bounded by compactness. For |x|<1, the Poisson formula applies at every real point on the segment between zero and x. Continuous integrability on the closed time-angle rectangle justifies exchanging the integrals with their orientation for negative x. Subtracting the actual B_b representation gives the exact boundary pairing with A_x-B_b. The integral triangle inequality, the actual closed-disk norm and normalized L1 control yield the estimate. Continuity of H extends the inequality to x=-1 and x=1. The case b=1 is already included in the primitive representation. No boundary Poisson formula, coefficient restriction or hypothesis about a kernel norm is imposed.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("schur-integrated-kernel-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
