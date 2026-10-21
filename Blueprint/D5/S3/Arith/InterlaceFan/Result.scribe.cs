using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.InterlaceFan;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal interlace fan faces containing nonzero rational points.",
        H("Rational faces of the interlace fan"), Blocks(
            Describe.Lean(DescribeId.Create("interlace-minimal-rational-faces"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Result.result"),
                H("The rational-face classification"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/PrimeForms/mandel2019dragging")),
                Blocks(
                    Paragraph(Text("For every darga n at least two, a nonempty subset S of the certificate indices admits a nonzero rational point in its closed face if and only if S misses the entire root-order class of some divisor d of n. The maximal certificate sets with this property are exactly the complements of individual order classes. For every such complement, every nonzero rational point has strictly smaller functional values on all omitted indices and has rational interlace number. This proves the pinned classification answering section 10, Problem 3 of the cited article, with zero excluded because it belongs to every closed face.")),
                    Paragraph(Text("The order-one class consists only of index zero. At rational coordinates that functional is rational. If the maximizing set meets every order class, cyclotomic conjugacy propagates this same rational value to every certificate, and Fourier injectivity forces the point to vanish. Conversely the rational Ramanujan coordinates give the two values totient(d)/2 and (totient(d)-n)/2, so missing an order class suffices. Exact real certificate-set realization identifies reversal of face inclusion with inclusion of certificate sets.")),
                    Paragraph(Text("Rationality of the maximum follows at index zero unless the omitted class has order one. In that case the weighted zero-sum identity expresses the common maximum at all positive indices as minus the rational zero-index value divided by a positive rational sum of weights. A tie at any omitted index then propagates through that entire order class and would force all values equal, contradicting the nonzero condition.")),
                    Paragraph(Text("The formal conclusion classifies maximal certificate sets and gives strict inequalities and rational maxima. Face dimensions and counts of geometric faces are consequences of the orthant interpretation; they are not additional formal assertions of this theorem. The polynomial corresponding to the sigma coordinates has twice the middle coordinate as its middle coefficient when n is even."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mandel-robins-2019-minimal-rational-foic-faces"),
                    ResolutionKind.Proved)))));
}
