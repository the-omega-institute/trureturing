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
                + "as the only remaining case after the product cases are separated. The finite "
                + "incidence dichotomy and the resulting regular-case cancellation theorem are "
                + "recorded separately below.")),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("column-count"),
                DeclarationHandle.Create(Owner + "columnCount"),
                H("Count occupied rows in a column"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "columnCount(A,j) is the cardinality of the Fin 3 row set whose section "
                    + "contains column j."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("six-point-incidence-dichotomy"),
                DeclarationHandle.Create(Owner + "six_point_incidence_dichotomy"),
                H("Six-point incidence dichotomy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A six-point 3-by-3 incidence table with every nonempty row and column "
                    + "containing at least two points is either a two-row product, a two-column "
                    + "product, or has exactly two points in every row and every column. The "
                    + "statement is a finite enumeration and supplies the case split before the "
                    + "character argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-regular-three-by-three-section-cancellation"),
                DeclarationHandle.Create(Owner + "no_regular_three_by_three_section_cancellation"),
                H("Regular incidence cannot cancel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every row and column has exactly two points, then no unit-modulus phase "
                    + "assignment can make every row section sum to zero. The proof uses the "
                    + "permutation normal form, restores the erased phase with "
                    + "Finset.sum_erase_add, and forces all phases and their total to vanish."))),
                DescribeRole.Theorem)
        )));
}
