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
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula l, Formula r) => Seq(l, Sp, Eq, Sp, r);
    private static Formula Term => Call("boundaryTerm", B, T, J);
    private static Formula Kernel(Formula t) => Call("boundaryKernel", B, t);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula Twoj(Formula n) => Seq(D(2), J, Plus, n);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Fourier kernel has a uniformly convergent series, reflection symmetry and the required sign on the full closed parameter range.",
        H("The boundary kernel of the imaginary-axis primitive average"), Blocks(
            Entry("term", "boundaryTerm", "The actual Fourier term",
                Disp(All("b", R, All("t", R, All("j", N, Eqn(Term,
                    Seq(Frac, Grp(D(2), Pow(Grp(Minus, D(1)), Seq(J, Plus, D(1))), Pow(B, Twoj(D(2)))),
                        Grp(Grp(Twoj(D(2))), Grp(Twoj(D(3)))), Call("cos", Seq(Grp(Twoj(D(1))), T)))))))),
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
                        Call("boundaryKernel"), Call("closedParameterStrip")))))),
                "For b in [0,1], the angle function is continuous, B_b(pi-t)=-B_b(t), and cos(t) B_b(t) is nonpositive. Partial sums converge uniformly on the full strip [0,1] times the real line. For b<1, the proof integrates the actual geometric cosine series, obtaining B_b(t)=-2b squared cos(t) times the integral from zero to one of u(1-u)(1+b squared u squared)/((1-b squared u squared) squared+4b squared u squared cos(t) squared). The integrand is nonnegative. Continuity in b extends the sign to b=1, including cos(t)=0. This does not yet give the entire-function primitive representation, mean-zero identity, sharp kernel size or the sharp error estimate.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("schur-boundary-kernel-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
