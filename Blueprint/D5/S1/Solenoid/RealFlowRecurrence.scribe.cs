using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class RealFlowRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial times recur to zero along the faithful solenoid real flow.",
        H("Factorial Recurrence and Solenoid Real-Flow Non-Embedding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorial-times-return-to-zero-in-the-solenoid"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/RealFlowRecurrence."
                        + "realFlow_factorial_tendsto_zero"),
                H("Factorial times return to zero in the solenoid"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    F.Id("realFlow"), Open, F.Id("n"), Bang, Close,
                    Sp, Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a positive modulus m. Once n is at least m, divisibility of "
                            + "factorials writes n factorial as m times an integer, so the "
                            + "m-th additive-circle coordinate of the real flow is exactly "
                            + "zero. Thus every coordinate is eventually constant at zero.")),
                    Paragraph(Text(
                        "The induced subtype topology and the product convergence criterion "
                            + "lift these coordinatewise limits to convergence in the "
                            + "universal solenoid. The pinned library supplies factorial "
                            + "divisibility and product-neighborhood convergence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-faithful-real-flow-is-not-an-embedding"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/RealFlowRecurrence."
                        + "realFlow_injective_not_isEmbedding"),
                H("The faithful real flow is not an embedding"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Injective")), Open,
                    F.Id("realFlow"), Close, Sp, Land, Sp, Neg,
                    Operatorname, Grp(F.Id("IsEmbedding")), Open,
                    F.Id("realFlow"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Injectivity is the established trivial-kernel theorem for the real flow. "
                        + "If the flow were a topological embedding, it would reflect the "
                        + "factorial recurrence to convergence of the real factorial times at "
                        + "zero. But each factorial dominates its index, so the same sequence "
                        + "diverges to positive infinity, giving incompatible eventual bounds."))),
                DescribeRole.Theorem))));
}
