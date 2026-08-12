using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class EntropyDivergenceIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Divergence from the uniform law equals the finite Shannon entropy deficit in nats.", H("The Entropy-Divergence Consistency Identity"), Blocks(
            Describe.Lean(DescribeId.Create("uniform-divergence-is-the-entropy-deficit"), DeclarationHandle.Create("D5/S3/Entropy/EntropyDivergenceIdentity.kl_divergence_uniform_eq"), H("Divergence from uniform is the entropy deficit"), StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Nonempty")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open,
                    F.Id("p"), Vert, Vert, Sp,
                    Open, F.Id("i"), Mapsto, Sp,
                    Operatorname, Grp(F.Id("card")), Open, Iota, Close,
                    Caret, Grp(Minus, D(1)), Close, Close, Eq,
                    Log, Open,
                    Operatorname, Grp(F.Id("card")), Open, Iota, Close,
                    Close, Minus,
                    F.Id("H"), Open, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "The theorem identifies the divergence of p from the uniform law with " +
                        "the entropy deficit log |iota| - H(p). Both sides use the repository's " +
                        "existing imported definitions, klDivergence and shannonEntropy; this " +
                        "module defines nothing of its own. The units are nats, consistent with " +
                        "klDivergence and shannonEntropy.")),
                    Paragraph(Text(
                        "This equality is a consistency pin between the two definitions. On the " +
                        "probability simplex, it fixes shannonEntropy pointwise, but only because " +
                        "klDivergence is independently attested by other frozen identities. The " +
                        "anchor is klDivergence; this is a pin between the two definitions, not an " +
                        "isolated certificate of entropy.")),
                    Paragraph(Text(
                        "The residual limitation is plain: the identity is blind to every " +
                        "correction that vanishes on normalized inputs. For example, adding a " +
                        "multiple of (sum_i p(i) - 1) to shannonEntropy is invisible under the " +
                        "theorem's hypotheses, because the corrupted entropy agrees with the true " +
                        "one everywhere those hypotheses hold. Off-simplex behaviour therefore " +
                        "remains unpinned; the theorem does not fully machine-attest the entropy " +
                        "definition.")),
                    Paragraph(Text(
                        "The reference is specifically the uniform law i -> (card iota)^-1. The " +
                        "identity does not hold against a non-uniform reference. A definition " +
                        "named uniform is deliberately not frozen in this bucket: it has a single " +
                        "consumer, so the reference is written inline.")),
                    Paragraph(Text(
                        "The hypotheses are nonnegativity and normalization only, not strict " +
                        "positivity. Zero-mass letters are permitted, and their terms vanish. The " +
                        "Nonempty iota hypothesis is genuinely required, not decorative: the proof " +
                        "needs positive cardinality.")),
                    Paragraph(Text(
                        "The same relation is derived inside MaxEntropy's proof as a proof-local " +
                        "step, but that step is not citable from outside the proof. This theorem is " +
                        "the first citable source of the fact and introduces no new definition. " +
                        "Frozen modules cannot gain declarations, so the relation is re-proved " +
                        "here rather than lifted out of MaxEntropy."))), DescribeRole.Theorem))));
}
