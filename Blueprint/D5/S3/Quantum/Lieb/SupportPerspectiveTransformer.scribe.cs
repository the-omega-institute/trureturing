// Exact supported perspective transformer for finite positive matrix maps.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class SupportPerspectiveTransformerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact supported perspective transformer for positive finite matrix maps.",
        H("SupportPerspectiveTransformer"), Blocks(
            Describe.Lean(DescribeId.Create("supported-positive-map-transformer"),
                DeclarationHandle.Create("D5/S3/Quantum/Lieb/SupportPerspectiveTransformer.supportedPerspective_transformer"),
                H("Positive maps contract the supported perspective"),
                StatementSource.FromAuthor(Transformer()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite complex matrix algebras with carriers in Type u, "
                    + "let Phi be any complex-linear positive map and A,B be PSD, "
                    + "with ker B contained in ker A. Let f be continuous on [0,infinity) "
                    + "and satisfy the actual OperatorConvexOnAll.{u} supplier there. "
                    + "Write W_B=spectralInverseSqrt(B), the existing spectral inverse "
                    + "square root which is zero on the kernel. The expression "
                    + "persp(f,A,B) denotes sqrt(B) cfc(f,W_B A W_B) sqrt(B). "
                    + "The conclusion below assumes no complete positivity, unitality "
                    + "or trace preservation of Phi, faithfulness, commutation, or "
                    + "restriction on f(0). Empty carriers and Phi(B)=0 are included.")),
                    Paragraph(Text(
                    "The mixed products sqrt(B) W_B and W_B sqrt(B) equal the "
                    + "existing spectralSupport(B), by finite spectral multiplication. "
                    + "The complement I-support(B) maps into ker B, so the exact "
                    + "kernel hypothesis gives both support identities for A and "
                    + "the reconstruction sqrt(B) (W_B A W_B) sqrt(B)=A. Apply "
                    + "the previously authored ambient positive-unital Jensen to "
                    + "X=W_B A W_B. Its scalar correction localizes away on the "
                    + "output support under CFC, then vanishes after congruence "
                    + "by sqrt(Phi(B)). The remaining normalized image reduces to "
                    + "Phi(persp(f,A,B)) using signed sandwich support. Thus a "
                    + "negative value of f(0) does not require a positivity claim "
                    + "for f(X).")), Paragraph(Text(
                    "The analytic power supplier is the existing attributed Physlib "
                    + "transplant by Kei Tsukamoto, Kento Mori and Hayata Yamasaki, "
                    + "revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. "
                    + "PowerConvexity.condIciAll_rpow supplies all-Hilbert operator "
                    + "convexity of x^(1+h) on [0,infinity) for 0<h<=1. For these h the affine "
                    + "correction g_h(x)=(x^(1+h)-x)/h is operator convex on that interval: "
                    + "subtract the affine operator argument in the power inequality "
                    + "and multiply by the positive scalar 1/h.")),
                    Paragraph(Text(
                    "UniformPowerSlope.rpow_slope_tendsto_uniformly reuses Alex "
                    + "Meiburg's estimate from Physlib QuantumInfo/Entropy/Relative.lean "
                    + "at the same revision, under Apache-2.0. It supplies uniform "
                    + "convergence of g_h(x) to x log x on every [0,K], including "
                    + "x=0. For a positive bounded operator S its entire real spectrum "
                    + "lies in [0,norm(S)]. Mathlib.tendsto_cfc_fun therefore passes "
                    + "this uniform convergence through CFC. Apply it to A, B and "
                    + "(1-t)A+tB; closed operator order passes their Jensen inequality "
                    + "to the limit. This establishes the actual OperatorConvexOnAll "
                    + "condition for x log x in every original Hilbert universe. "
                    + "The limit is cfc(x log x,S), with value zero at zero. Spectra "
                    + "accumulating at zero are allowed; no bounded CFC logarithm "
                    + "or factorization as S times log(S) is used.")),
                    Paragraph(Text(
                    "For the concrete entropy application let a,b be arbitrary "
                    + "finite decidable types in the same universe, including empty "
                    + "types. Let Phi be positive and complex-linear, and require "
                    + "trace(Phi(Z))=trace(Z) for every matrix Z. For PSD A,B assume "
                    + "exactly ker B contained in ker A. Set f(x)=x log x, using "
                    + "Real.continuous_mul_log for continuity and the preceding "
                    + "all-Hilbert limit for operator convexity. The transformer "
                    + "gives persp(f,Phi(A),Phi(B)) <= Phi(persp(f,A,B)). "
                    + "Apply the positive trace map, substitute the literal trace "
                    + "preservation law, and take real parts. The result is "
                    + "Re trace(persp(f,Phi(A),Phi(B))) <= Re trace(persp(f,A,B)). "
                    + "No complete positivity, unitality, normalization, invertibility "
                    + "or commutation is required. This is the supported maximal, "
                    + "or Belavkin-Staszewski-type, entropy perspective. It is not "
                    + "an identification with Umegaki entropy, and the finite "
                    + "matrix conclusion is not an infinite-dimensional quantum "
                    + "data-processing theorem."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Mat(string n) => Call("Matrix", F.Id(n), F.Id(n), Complex);
    private static Formula Binder(string name, Formula type) => Seq(F.Id(name), Colon, Sp, type, Comma, Esc);
    private static Formula Instance(string name, string n) => Seq(OpenBracket, Call(name, F.Id(n)), CloseBracket, Comma, Sp);
    private static Formula Carrier(string n) => Seq(Binder(n, Call("Type", F.Id("u"))),
        Instance("Fintype", n), Instance("DecidableEq", n));
    private static Formula Transformer() => Disp(Seq(Forall, Sp, Binder("u", Call("Level")),
        Carrier("n"), Carrier("m"), Binder("f", Seq(Real, Sp, To, Sp, Real)),
        Binder("Phi", Call("PositiveLinearMap", Complex, Mat("n"), Mat("m"))),
        Binder("A", Mat("n")), Binder("B", Mat("n")),
        Call("OperatorConvexOnAll", F.Id("u"), Call("Ici", D(0)), F.Id("f")), Comma, Sp,
        Call("ContinuousOn", F.Id("f"), Call("Ici", D(0))), Comma, Sp,
        Call("PSD", F.Id("A")), Comma, Sp, Call("PSD", F.Id("B")), Comma, Sp,
        Call("ker", F.Id("B")), Subseteq, Sp, Call("ker", F.Id("A")), Sp, Implies, Sp,
        Call("persp", F.Id("f"), Call("Phi", F.Id("A")), Call("Phi", F.Id("B"))), Le,
        Call("Phi", Call("persp", F.Id("f"), F.Id("A"), F.Id("B")))));
}
