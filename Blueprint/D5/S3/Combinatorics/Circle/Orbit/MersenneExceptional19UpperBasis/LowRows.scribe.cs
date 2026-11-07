using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis;

internal sealed class LowRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual low affine rows and the remaining doubling relations — UNCOMPILED source preparation.",
        H("Actual low affine rows and the remaining doubling relations"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-low-row-table"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/LowRows.actual_low_row_table"),
                H("actual low row table"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual low G row gives F2=2f1. The remaining three physical affine rows are read from their modulo-four digits and integer floors, using the corrected ladders. This proves the low table from selected annihilation, rather than assuming its entries."))), DescribeRole.Theorem),

            Paragraph(Text("Reading the high tail with its low two digits. The proved corrected ladders reduce a valid d-bit word to its bit-0 label, bit-1 label and floor(word/4) times its level-2 label. The correction vanishes at levels 0,1,2 because d>=12. The sum-zero level-2 triple then gives the two high coefficients floor(L/4)-floor(U/4) and floor(M/4)-floor(U/4). affine_low_read applies this to the original actual affine words, using the proved integer correction incidence.")),
            Paragraph(Text("The actual G row at j=1. T0 and T1 are evaluated as the selected triple indicators. The j=1 upper G row minus the selected base row has bit signature (-1,1,1) and reads F2-2x after T1, where x=f1. Consequently F2=2x. This equality is obtained from a coefficient-one relation, with no cancellation of 2 in A.")),
            Paragraph(Text("Deriving the low table. With k=s/2 and eta=(a+1)/4, the actual words for the base, F_top and R_a have modulo-4 triples (3,0,1), (0,1,2) and (2,3,0). The source proves their integer floor differences and derives the readouts kx+eta G2-y, kx+eta G2+y-z and kx+(eta-1)G2+y+z. The residue facts a=b=3 mod 4 and s=2 mod 4 follow uniformly from parameter_exact and eighth_facts.")),
            Paragraph(Text("Consumer and limits. Reconstruction consumes the table to get z=2y, G2=4y and kx+ay=0, then expresses every coordinate using u=f0,x=f1,y=g0 and theta. The table is not a standalone assumed boundary certificate. These scripts remain UNCOMPILED; their actual elaboration and scalar normalization require the caller verification."))), []));
}
