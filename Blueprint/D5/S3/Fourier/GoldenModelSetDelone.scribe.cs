using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GoldenModelSetDeloneDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Fourier/GoldenModelSetDelone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete golden model set has explicit separation and global covering witnesses.",
        H("An Explicit Golden Delone Set"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-norm-separation-bound"),
                DeclarationHandle.Create(Gid + "norm_separation"),
                H("Internal displacement bounds force physical separation"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("u"), Comma, F.Id("v"), InMacro, Call("GoldenInt"), Comma, Sp,
                    F.Id("u"), Neq, F.Id("v"), Comma, Sp,
                    F.Id("B"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Call("abs", Seq(Call("internal", F.Id("u")), Minus,
                        Call("internal", F.Id("v")))), Le, F.Id("B"), Sp, Rightarrow, Sp,
                    F.D(1), Le, Call("abs", Seq(Call("emb", F.Id("u")), Minus,
                        Call("emb", F.Id("v")))), Times, F.Id("B")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Internal(u) is embedding(conj(u)), and emb is the distinguished real "
                    + "embedding. The real bound B is arbitrary; no positivity hypothesis is "
                    + "needed. The nonzero integer norm of u-v has absolute value at least one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-golden-model-set-delone"),
                DeclarationHandle.Create(Gid + "exists_golden_modelSet_delone"),
                H("Packing radius one half and covering radius three"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("D"), InMacro, Call("DeloneSet", F.Id("R")), Comma, Sp,
                    Call("carrier", F.Id("D")), Eq,
                    Call("modelSet", F.Id("W")), Sp, Land, Sp,
                    Call("packingRadius", F.Id("D")), Eq, Frac, Grp(F.D(1)), Grp(F.D(2)),
                    Sp, Land, Sp, Call("coveringRadius", F.Id("D")), Eq, F.D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are no hypotheses. Here R is the real line, W is the existing "
                        + "closed goldenWindow [-phi^(-2), phi^(-1)], and modelSet is "
                        + "D5.S1.Scale.modelSet: all physical embeddings of golden integers "
                        + "whose conjugate embedding belongs to W. The radii are nonnegative reals.")),
                    Paragraph(Text(
                        "Distinct selected points are at least one apart by the norm bound. "
                        + "For every real x, put q=2*phi-1, b=floor(x/q), and "
                        + "a=floor(phi-1-b*(1-phi)). The golden integer (a,b) has conjugate "
                        + "coordinate in W and physical distance at most three from x. "
                        + "The scheme adapter transports these witnesses into Certificate, "
                        + "whose existing toDeloneSet conversion produces the asserted bundle.")),
                    Paragraph(Text(
                        "The carrier is bi-infinite. This result makes no relative-density "
                        + "claim about the natural-number-indexed betaGolden image."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
