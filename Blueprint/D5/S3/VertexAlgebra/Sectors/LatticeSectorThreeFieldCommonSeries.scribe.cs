using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorThreeFieldCommonSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six actual canonical three-field products have a common vector series.",
        H("Three Canonical Sector Fields"), Blocks(
            Paragraph(Text("Take arbitrary ordinary even integral lattice data D, three charges alpha,beta,gamma and arbitrary oscillator descendants u,v,t. The labelled fields are precisely Y D applied to their canonical sector inclusions. Charges, states and field values may repeat. Degenerate and indefinite forms and rank zero are included; no inverse Gram matrix is used.")),
            Describe.Lean(DescribeId.Create("actual-three-field-common-series"),
                DeclarationHandle.Create(Prefix + "actual_three_field_common_series"),
                H("All six orders on an arbitrary fourth-sector state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("There is one locality order k for the three fields before the fourth charge delta and state w are chosen. For each delta,w there are nonnegative cutoffs a and a native MvPowerSeries in three variables with coefficients in the common total-charge oscillator sector. Each original canonical mode vanishes on w at every integer mode at least its cutoff.")),
                    Paragraph(Text("At every signed exponent vector e, clearing by Q and evaluating at e-a gives the signed extension of this same P for each of the six orders 012,021,102,120,201,210. The products are the literal three nested canonical operators, with the exponent attached to its original label. inclusion_canonical and its charge_homogeneity supplier identify each nested product with the original Carrier field word; permutation invariance of total charge puts all six in one sector. Projection commutes with finite convolution and signed extension.")),
                    Paragraph(Text("This endpoint requires no locality certificate from its caller: stateField_locality discharges it for the actual fields, and the actual VertexOperator truncation discharges the input cutoffs. It proves neither associator nor pentagon, hexagon, four-object sewing or convergence on an arbitrary algebraic dual. Full charged module categories, symmetry anomalies, Monster realization, CFT, string theory and AdS/CFT remain further mathematical obligations."))), DescribeRole.Theorem),
            Paragraph(Text("Classical lattice and formal-locality sources are those of the imported Bakalov-Kac, Matsuo-Nagatomo and Carnahan suppliers. The construction asserts no new literature theorem.")))));
}
