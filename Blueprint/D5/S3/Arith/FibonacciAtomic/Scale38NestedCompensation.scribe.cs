using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class Scale38NestedCompensationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nested left combs share a fixed root compensation position and a literal raw scan.",
        H("Nested Compensation"),
        Blocks(Describe.Lean(
            DescribeId.Create("nested-compensation-raw-acquisition"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation.result"),
            H("Complete sources and exact requested-address bills"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every positive integer k, the baseline, the k enlarged-slot rows, and "
                + "the k contracted-left-comb rows are distinct actual third substitution images. "
                + "Each has the displayed unique complete preimage, with composition (k+1,2). "
                + "Their image composition is (k+5,2k+8), with 3k+13 leaves. Every pair is "
                + "nonconflicting, including pairs whose left combs end at different depths.")),
                Paragraph(Text(
                "The scan requests L followed by t right turns and LLR, for t from zero through k. "
                + "Alpha replies continue the scan. A branch selects the enlarged slot at t; "
                + "an absent reply at t greater than zero selects contraction depth t-1. "
                + "All alpha replies select the baseline. Every other reply starts total tree "
                + "acquisition. A selection always starts a complete labelled-leaf test, with "
                + "a mismatch also starting total acquisition.")),
                Paragraph(Text(
                "The same controller terminates and decides third-image membership for every "
                + "finite input tree. On the baseline its distinct requested addresses are exactly "
                + "the leaves. On an enlarged-slot or contraction row they are the leaves together "
                + "with its single branch or absent exit address. The earlier scan addresses are "
                + "actual alpha leaves of that input, and the exit address is not a leaf. "
                + "Thus the baseline costs 3k+13 and every exceptional row costs 3k+14."))),
            DescribeRole.Theorem))));
}
