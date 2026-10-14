using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalSupportConflictDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalSupportConflict.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three original support factors cannot coexist in any full event.",
        H("An exact conflict in the original EJM inflation supports"),
        Blocks(
            Paragraph(Text("The triangle support contains 132 actual local assignments, obtained from original rows 104, 259, 332 and 464. The singleton support contains 168 assignments from original rows 220 and 252. Each support retains its complete orbit under all twelve local-coordinate actions and all twenty-four simultaneous outcome permutations. The literal original marginal maps are used in their original order. No coordinate-zero normalization is imposed.")),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("A common event for original factors 24, 2 and 3"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim asserts the existence of one full twenty-coordinate, four-outcome event in singleton marginal 8 and triangle marginals 2 and 3. Singleton 8 is factor 24 in the original sixteen-plus-sixteen numbering. Compatibility quantifies over every coordinate of each actual local row."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The actual empty natural join refutes the common event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel evaluates the exact finite join of these three complete supports. General join soundness preserves any putative full event through both joins, contradicting the empty final relation. This excludes simultaneous inside membership; it does not establish the original uniform positive EJM score margin, nonlocality or a strict noise region. Those require the subsequent exact averaging and dual-certificate proof."))),
                DescribeRole.Theorem))));
}
