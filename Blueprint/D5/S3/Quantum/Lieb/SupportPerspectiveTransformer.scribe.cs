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
                    "The three mathematical modules have passed explicit targeted "
                    + "Lean builds. Their joint scoped report records only propext, "
                    + "Quot.sound and Classical.choice. Information-audit binding "
                    + "is assessed separately and is not claimed complete here. "
                    + "The finite-effect to rectangular-isometry to endomorphism "
                    + "contraction bridge remains an explicit authored dependency; "
                    + "it is not an assumed new axiom. The analytic supplier is "
                    + "the existing attributed Physlib transplant by Kei Tsukamoto, "
                    + "Kento Mori and Hayata Yamasaki, revision "
                    + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. "
                    + "No official acceptance or mathematical novelty is asserted "
                    + "by this document."))),
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
