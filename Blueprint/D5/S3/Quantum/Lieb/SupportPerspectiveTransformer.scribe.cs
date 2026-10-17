// Source candidate; current Scribe compilation and emission are pending.
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class SupportPerspectiveTransformerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proposed exact supported perspective transformer for positive finite matrix maps.",
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
                    "All source, including the frozen Jensen/support dependencies, "
                    + "still requires actual Lean elaboration and kernel checking. "
                    + "The finite-effect to rectangular-isometry to endomorphism "
                    + "contraction bridge remains an explicit authored dependency; "
                    + "it is not an assumed new axiom. The analytic supplier is "
                    + "the existing attributed Physlib transplant by Kei Tsukamoto, "
                    + "Kento Mori and Hayata Yamasaki, revision "
                    + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. "
                    + "No binding, validation, official acceptance or mathematical "
                    + "novelty is asserted by this proposed Scribe source."))),
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

    private static Formula Transformer() => Seq(
        Call("persp", F.Id("f"), Call("Phi", F.Id("A")), Call("Phi", F.Id("B"))), Le,
        Call("Phi", Call("persp", F.Id("f"), F.Id("A"), F.Id("B"))));
}
