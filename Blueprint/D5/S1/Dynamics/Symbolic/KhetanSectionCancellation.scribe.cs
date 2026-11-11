using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanSectionCancellationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/KhetanSectionCancellation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 3-by-3 two-point section pattern is incompatible with character cancellation.",
        H("Six-point section cancellation"),
        Blocks(
            Paragraph(Text(
                "The non-product six-point incidence pattern has row pairs 01, 02, and 12. "
                + "The three corresponding character sums cannot all vanish when the phases have "
                + "unit modulus. A finite regular-incidence classification identifies this pattern "
                + "as the only remaining case after the product cases are separated.")),
            Describe.Lean(
                DescribeId.Create("no-triangle-section-cancellation"),
                DeclarationHandle.Create(Owner + "no_triangle_section_cancellation"),
                H("Triangle cancellation obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Unit-modulus phases cannot have zero sums on all three two-point sections "
                    + "01, 02, and 12."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regular-three-by-three-incidence"),
                DeclarationHandle.Create(Owner + "regular_three_by_three_incidence"),
                H("Regular incidence normal form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every row and every column of a 3-by-3 incidence matrix has two "
                    + "occupied points, the row complements are indexed by a permutation of the "
                    + "three missing columns."))),
                DescribeRole.Theorem)
        )));
}
