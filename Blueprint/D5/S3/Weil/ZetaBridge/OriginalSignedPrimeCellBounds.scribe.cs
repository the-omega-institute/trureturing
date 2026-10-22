using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalSignedPrimeCellBoundsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/OriginalSignedPrimeCellBounds.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed-cell soundness for arbitrary Row and Cell lists bounds the continuous row sum from a connected rational chain and row monotonicity. The complex L2 estimate applies this result to the original arithmetic data.",
        H("OriginalSignedPrimeCellBounds"),
        Blocks(
                Paragraph(Text("Closed-cell soundness for arbitrary Row and Cell lists bounds the continuous row sum from a connected rational chain and row monotonicity. The complex L2 estimate applies this result to the original arithmetic data.")),
                Paragraph(Text("A row records q, p, k and the two nonnegative integer logarithm ceilings a and b. The scale is one million. For r in [1,71], plus(t,r)=(r*b+a)/(1000000*(r+1)) and minus(t,r)=(r*a+b)/(1000000*(r+1)). The assumption a<=b makes the first increasing and the second decreasing. The row sum retains both weak tests q*r<=71 and q<=71*r.")),
                Paragraph(Text("For a rational closed cell [l,u], plus is evaluated at u and minus at l. The accept flags use l for the plus support test and u for the minus support test, so each cell overestimates both endpoints and every point between them. Cell.valid recomputes all four prefix sums from the supplied variable row list and checks the single cross-multiplied strict inequality, with positive denominators.")),
                Paragraph(Text("CellCertificate supplies validity for every cell and a nonempty exact endpoint chain from 1 to 71. The recursive chain proof gives closed coverage, including the final endpoint. The proof of roundedRow_lt_eighty uses that coverage, row monotonicity, and the integer inequality to obtain a continuum bound; no real sample or finite-matrix Schur estimate replaces this inference.")),
                Describe.Lean(DescribeId.Create("Row"),
                    DeclarationHandle.Create(Owner + "Row"), H("Row"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The reusable arithmetic row schema; the concrete table is local to original_prime80."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("Cell"),
                    DeclarationHandle.Create(Owner + "Cell"), H("Cell"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("A rational closed cell with natural numerators and positive-denominator obligations in Cell.valid."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("CellCertificate"),
                    DeclarationHandle.Create(Owner + "CellCertificate"), H("CellCertificate"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The validity and connected-chain premises for variable data; no successful concrete input is asserted by this structure."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("plus"),
                    DeclarationHandle.Create(Owner + "plus"), H("plus"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The increasing coefficient (r*b+a)/(1000000*(r+1)) for the positive translation."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("minus"),
                    DeclarationHandle.Create(Owner + "minus"), H("minus"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The decreasing coefficient (r*a+b)/(1000000*(r+1)) for the negative translation."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("plus-nonneg"),
                    DeclarationHandle.Create(Owner + "plus_nonneg"), H("plus nonneg"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The positive-translation coefficient is nonnegative for every nonnegative r."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("minus-nonneg"),
                    DeclarationHandle.Create(Owner + "minus_nonneg"), H("minus nonneg"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The negative-translation coefficient is nonnegative for every nonnegative r."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("rowTerm"),
                    DeclarationHandle.Create(Owner + "rowTerm"), H("rowTerm"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Both signed coefficients are retained with their weak support tests."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("roundedRow"),
                    DeclarationHandle.Create(Owner + "roundedRow"), H("roundedRow"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The sum of both signed coefficient envelopes over every supplied row."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("roundedRow-lt-eighty"),
                    DeclarationHandle.Create(Owner + "roundedRow_lt_eighty"), H("roundedRow lt eighty"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Soundness from a variable exact closed chain and row monotonicity to every real r in the full closed interval [1,71]."))), DescribeRole.Theorem))));
}
