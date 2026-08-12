using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CarryCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("A fixed-width recurrence makes a consecutive block and its carry digit equal in weight.",
H("Recurrence Carry Cancellation"),
Blocks(
            Describe.Lean(
                DescribeId.Create("recurrence-carry-preserves-weight"),
                DeclarationHandle.Create("D5/S1/Recurrence/CarryCancellation.recurrence_carry_preserves_weight"),
                H("A recurrence redeems its forbidden consecutive block"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("w"), Open, F.Id("s"), Plus, F.Id("r"), Close,
                    Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Lt, F.Id("r")), Sp,
                    F.Id("w"), Open, F.Id("s"), Plus, F.Id("i"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite digit state carries natural multiplicities, while an arbitrary "
                        + "additive sequence assigns weights to positions. The local redex occupies "
                        + "the consecutive positions s through s+r-1, and its carry image occupies "
                        + "only position s+r. The recurrence hypothesis identifies their weights. "
                        + "Additivity then preserves the value after adjoining any untouched state.")),
                    Paragraph(Text(
                        "Widths two and three give the Fibonacci and Tribonacci cancellation "
                        + "patterns once their respective recurrences are supplied. Pinned Mathlib "
                        + "provides Finsupp.weight, Finsupp.weight_single, finite-sum additivity, and "
                        + "Nat.fib_add_two. Searches found no fixed-width recurrence-carry theorem "
                        + "and no Tribonacci declaration, so the uniform local rewrite theorem is "
                        + "new proof content rather than a thin wrapper."))),
                DescribeRole.Theorem))));
}
