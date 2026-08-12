using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class MirrorPairEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mirror-pair exponential envelope is twice the hyperbolic cosine.",
        H("Mirror-Pair Exponential Envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-mirror-pair-envelope-is-twice-the-hyperbolic-cosine"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/MirrorPairEnvelope.mirror_pair_envelope_eq_two_cosh"),
                H("The mirror-pair envelope is twice the hyperbolic cosine"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Beta, Comma, F.Id("u"), InMacro,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Operatorname, Grp(F.Id("exp")), Open,
                    Open, Beta, Minus, Frac, Grp(D(1)), Grp(D(2)), Close,
                    F.Id("u"), Close,
                    Sp, Plus, Sp,
                    Operatorname, Grp(F.Id("exp")), Open, Minus,
                    Open, Beta, Minus, Frac, Grp(D(1)), Grp(D(2)), Close,
                    F.Id("u"), Close,
                    Sp, Eq, Sp, D(2),
                    Operatorname, Grp(F.Id("cosh")), Open,
                    Open, Beta, Minus, Frac, Grp(D(1)), Grp(D(2)), Close,
                    F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary real beta and u, the exponential branch at "
                        + "(beta - 1/2)u plus its reflected branch equals twice the "
                        + "hyperbolic cosine at the same argument. Pinned Mathlib provides "
                        + "Real.cosh_eq, so the Lean proof is a thin wrapper around that "
                        + "identity followed only by ring normalization.")),
                    Paragraph(Text(
                        "This is a partial closure of the source mirror-pair certificate. "
                        + "The lower bound, strict monotonicity, numerical evaluation, "
                        + "evenness residual, conservation claim, and physical, diffraction, "
                        + "ledger, and concluding interpretations remain unresolved."))),
                DescribeRole.Theorem))));
}
