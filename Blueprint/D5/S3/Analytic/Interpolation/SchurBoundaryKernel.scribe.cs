using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class SchurBoundaryKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Interpolation/SchurBoundaryKernel.";
    private static Formula B => F.Id("b");
    private static Formula T => F.Id("t");
    private static Formula J => F.Id("j");
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Functions => Seq(C, Sp, To, Sp, C);
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula l, Formula r) => Seq(l, Sp, Eq, Sp, r);
    private static Formula Integral(string v, Formula lo, Formula hi, Formula body) =>
        Call("integral", lo, hi, Seq(Open, F.Id(v), Sp, Colon, Sp, R, Close, Sp, Mapsto, Sp, body));
    private static Formula Term => Call("boundaryTerm", B, T, J);
    private static Formula Kernel(Formula t) => Call("boundaryKernel", B, t);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula Twoj(Formula n) => Seq(D(2), J, Plus, n);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Fourier kernel has a uniformly convergent series, reflection symmetry and the required sign on the full closed parameter range.",
        H("The boundary kernel of the imaginary-axis primitive average"), Blocks(
            Entry("term", "boundaryTerm", "The actual Fourier term",
                Disp(All("b", R, All("t", R, All("j", N, Eqn(Term,
                    Seq(Frac, Grp(D(2), Pow(Seq(Open, Minus, D(1), Close), Seq(J, Plus, D(1))), Pow(B, Twoj(D(2)))),
                        Grp(Open, Twoj(D(2)), Close, Open, Twoj(D(3)), Close), Call("cos", Seq(Open, Twoj(D(1)), Close, T)))))))),
                "The term is 2(-1)^(j+1)b^(2j+2) cos((2j+1)t)/((2j+2)(2j+3)). These are the coefficients of B_b in the source; no sign or size contract is postulated.", DescribeRole.Definition),
            Entry("kernel", "boundaryKernel", "The source Fourier series",
                Disp(All("b", R, All("t", R, Eqn(Kernel(T), Call("tsum", Call("boundaryTerm", B, T)))))),
                "The kernel is the real tsum of its actual terms. A summable inverse-square majorant controls the series uniformly on b in [0,1] and all real angles.", DescribeRole.Definition),
            Entry("control", "boundary_kernel_control", "Uniform convergence, reflection and sign including b=1",
                Disp(All("b", R, All("t", R, Seq(
                    D(0), Sp, Le, Sp, B, Sp, Le, Sp, D(1), Sp, Implies, Sp,
                    Call("Continuous", Call("boundaryKernel", B)), Sp, Land, Sp,
                    Eqn(Kernel(Seq(Call("pi"), Minus, T)), Seq(Minus, Kernel(T))), Sp, Land, Sp,
                    Call("cos", T), Kernel(T), Sp, Le, Sp, D(0), Sp, Land, Sp,
                    Call("UniformConvergenceOn", Call("partialSumsOfBoundaryTerms"),
                        Call("boundaryKernel"), Call("closedParameterStrip")), Sp, Land, Sp,
                    Call("ContinuousOn", Call("boundaryKernelOfPair"), Call("closedParameterStrip")),
                    Sp, Land, Sp, Eqn(Call("integral", D(0), Seq(D(2), Pi), Call("boundaryKernel", B)), D(0)),
                    Sp, Land, Sp, Call("abs", Kernel(T)), Sp, Le, Sp,
                    Frac, Grp(D(3,0,6,7)), Grp(D(8,1,0,0)), Sp, Land, Sp,
                    Frac, Grp(D(3,0,6,7)), Grp(D(8,1,0,0)), Sp, Lt, Sp,
                    Frac, Grp(D(1,9)), Grp(D(5,0)))))),
                "For b in [0,1], the angle function is continuous, B_b(pi-t)=-B_b(t), and cos(t) B_b(t) is nonpositive. Partial sums converge uniformly on the full strip [0,1] times the real line. For b<1, the proof integrates the actual geometric cosine series, obtaining B_b(t)=-2b squared cos(t) times the integral from zero to one of u(1-u)(1+b squared u squared)/((1-b squared u squared) squared+4b squared u squared cos(t) squared). The integrand is nonnegative. Continuity in b extends the sign to b=1, including cos(t)=0. The joint parameter-angle function is continuous on the full strip. Termwise cosine integration gives zero mean. The rational size estimate is |B_b(t)| <= 3067/8100 < 19/50. After y=bu the nonnegative integral is bounded by the integral of (1-y)q(y,c), c=|cos(t)|. On [0,1/3] this is at most 2y(1-y)(1-9y squared/10), whose integral is 667/8100. On [1/3,1] it is at most 3/8+y/8-3(y-1/3)(1-y)/16, whose integral is 8/27. Continuity includes b=1. The rational bound is sufficient for the integrated-kernel estimate. It does not assert the separate logarithm-arctangent constant C.", DescribeRole.Theorem),
            Entry("primitive", "boundary_primitive_representation", "The normalized entire primitive representation",
                Disp(All("h", Functions, All("H", Functions, All("b", R, Seq(
                    Call("Entire", F.Id("h")), Sp, Land, Sp,
                    Call("HasDerivativeEverywhere", F.Id("H"), F.Id("h")), Sp, Land, Sp,
                    Eqn(Call("H", D(0)), D(0)), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, B, Sp, Le, Sp, D(1), Sp, Implies, Sp,
                    Eqn(Seq(Frac, Grp(D(1)), Grp(D(2), B),
                            Integral("t", Seq(Minus, B), B, Call("H", Seq(F.Id("i"), T)))),
                        Seq(Frac, Grp(D(1)), Grp(D(2), Pi),
                            Integral("t", D(0), Seq(D(2), Pi),
                                Seq(Call("h", Call("circleMap", D(0), D(1), T)), Kernel(T)))))))))),
                "Let h be any entire complex-valued function and let H have complex derivative h everywhere and H(0)=0. Then the normalized integral of H(it) from -b to b is the circle pairing of h with the actual real Fourier kernel, for every 0<b<=1. The primitive is entire because it is complex differentiable everywhere; existence of a normalized entire primitive follows from the exact primitive theorem on the complex plane. For 0<b<1, the Cauchy mean formula gives the average of h(z)/(z-w). Applying it at w=ir and w=-ir, and conjugating only the rational kernel z/(1+r squared z squared) on the unit circle, gives its real-part pairing. Continuity and compact product integrability justify exchanging the time and angle integrals. The fundamental theorem of calculus applied to (1-t)(H(ibt)+H(-ibt)) identifies the resulting weighted integral. Real changes of variables give the displayed vertical-segment average. Joint continuity of the actual kernel and compact parameter integrals extend the identity to b=1. No conjugation identity for h or H is assumed, and all coefficients remain arbitrary complex numbers.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("schur-boundary-kernel-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
