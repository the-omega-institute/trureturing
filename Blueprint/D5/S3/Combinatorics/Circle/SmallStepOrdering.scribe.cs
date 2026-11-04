using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class SmallStepOrderingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite steps whose combined magnitudes fit the strip can be permuted between any legal start and their resulting legal endpoint.",
        H("Ordering pairwise compatible steps between two endpoints"),
        Blocks(
            Describe.Lean(DescribeId.Create("small-step-ordering-between-endpoints"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SmallStepOrdering.exists_order_between"),
                H("An order of all occurrences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any type of labels, integer weights f, finite list labels, capacity C and initial height h, suppose h and h+sum(labels.map(f)) are both in [0,C]. Suppose also that every positive step p and negative step n in the supplied list satisfy f(p)-f(n)<=C. Then a list word permuting exactly labels stays in [0,C] from h at every prefix. No distinctness or nonzero-weight assumption is required. Permutation preserves repetitions and all distinct physical labels even when their weights coincide.")),
                    Paragraph(Text("Induct on the number of remaining occurrences. If a negative step fits, remove it and recurse. Otherwise select any positive step p. If it overflows the capacity, the legal final endpoint forces some negative n to remain. Its failure to fit gives h+f(n)<0, while the positive failure gives h+f(p)>C, contradicting f(p)-f(n)<=C. If no positive step remains, all heights decrease monotonically to the prescribed legal endpoint. Each removal is certified by List.perm_cons_erase.")),
                    Paragraph(Text("For the centered doubling source with Q=2^(k-2) and C=2Q-1, every SMALL magnitude is at most Q-1. Opposite SMALL magnitudes therefore sum to at most 2Q-2<C. The theorem can order any specified complete physical SMALL list between proved legal endpoints. This supplies the bridge and tail orders in the two-opposite-LARGE exchange; it does not choose a subset, assert interval filling, pass any LARGE gate, extend an arbitrary mixed prefix, or resolve Circle Conjecture 3.1."))),
                DescribeRole.Theorem)), []));
}
