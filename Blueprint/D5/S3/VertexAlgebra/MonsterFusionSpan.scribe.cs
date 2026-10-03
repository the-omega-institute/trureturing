using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class MonsterFusionSpanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/MonsterFusionSpan.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/basak2017monstercharactercarry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven nonzero ground sections span every six-bit finite label, with one relation.",
        H("Seven Ground Sections and Finite Label Capacity"),
        Blocks(
            Paragraph(Text("Let E be the three-dimensional vector space over F_2 and let f "
                + "satisfy the finite sign-table equations. The label space is E times its "
                + "coordinate dual, and the ground section sends g to (g, f(g,-)).")),
            Describe.Lean(
                DescribeId.Create("seven-ground-sections-span-and-capacity"),
                DeclarationHandle.Create(Prefix + "fusion_span_and_capacity"),
                H("Six independent sections and the seven-point relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every sign table, six of the seven nonzero ground "
                    + "sections give a bijection from six binary coefficients to all labels. "
                    + "The sum of all seven sections is zero, and a relation among them "
                    + "forces all seven coefficients to agree. Thus this is the unique "
                    + "nonzero relation. There are 64 finite labels, with eight character "
                    + "values over each coarse defect. A three-bit encoding exists and no "
                    + "injective two-bit encoding of one fiber exists. The proof constructs the three missing character "
                    + "directions from the determinant carries, then uses the cubic-table "
                    + "classification to establish the seven-point relation. Basak's "
                    + "twisted-group-algebra calculation is historical context. The result "
                    + "does not establish a VOA realization or an actual fusion rule; the "
                    + "physical closure claim in the theory source remains conditional on "
                    + "that rule."))),
                DescribeRole.Theorem))));
}
