using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanSixCellResidueDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/KhetanSixCellResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact adjacent-column residue partitions force a horizontal or vertical period.",
        H("Residue propagation at the six-cell Nivat boundary"),
        Blocks(
            Paragraph(Text(
                "This module isolates the combinatorial core of the six-cell boundary discussed by Khetan. "
                + "The hypotheses are the exact XOR partition of every adjacent pair of columns and their disjointness. "
                + "The one-dimensional three-point tiling rigidity and the orbit-closure extraction remain separate obligations; "
                + "this theorem therefore records a conditional residue-propagation result rather than a resolution of the full open problem.")),
            Describe.Lean(
                DescribeId.Create("three-residue-column-dichotomy"),
                DeclarationHandle.Create(Owner + "three_residue_column_dichotomy"),
                H("Residue change forces a period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a column predicate T and integer residue labels r, assume that exactly one of the two adjacent "
                    + "column memberships holds precisely when y has residue r(x) modulo 3, and assume adjacent memberships "
                    + "are disjoint. If the labels are constant modulo 3, XOR cancellation gives T(x+2,y) ↔ T(x,y). "
                    + "If a label changes, the middle column is empty; periodicity propagates from that empty column in both "
                    + "integer directions, giving T(x,y+3) ↔ T(x,y) for every column."))),
                DescribeRole.Theorem)
        )));
}
