using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class PureCubicOrderCoordinateQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangular cubic-order lattice has two explicit cyclic quotient factors.",
        H("Pure Cubic Order Coordinate Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-cubic-order-coordinate-quotient"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/PureCubicOrderCoordinateQuotient.triangular_lattice_quotient"),
                H("Cyclic factors of the coordinate quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c and d be positive natural numbers, k an integer, and v either one "
                            + "or minus one. In the additive group of integer triples, let A be the "
                            + "subgroup of all integer combinations of (1,0,0), (0,c,0), and "
                            + "(-kv,-kvc,vd).")),
                    Paragraph(Text(
                        "There is an additive equivalence from the quotient by A to the product "
                            + "of the residue groups modulo c and modulo d. The proof computes "
                            + "the kernel of reduction of the second and third coordinates and "
                            + "proves that reduction is surjective. The unit sign v removes the "
                            + "off-diagonal term. The quotient is an additive group quotient; "
                            + "A is not asserted to be an ideal or a subring.")),
                    Paragraph(Text(
                        "For a pure cubic radicand B = c cubed times m times n squared, the "
                            + "intended maximal-order comparison sets d = c squared times n. "
                            + "Identifying the two field bases and the actual Lucas-block "
                            + "parameters is a separate obligation."))),
                DescribeRole.Theorem))));
}
