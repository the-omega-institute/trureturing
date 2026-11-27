using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class ChoiCongruencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Choi congruences and entanglement breaking"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-choicongruences-inputchoi"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi"),
                H("Input-first Choi matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The entry with row (i, u) and column (j, v) is the (u, v) entry of the image of the (i, j) matrix unit. This corresponds to the input-first convention in Section 2 of Devendra, Mallick and Sumesh (2023)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-choicongruences-iskeb"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.IsKEB"),
                H("Entanglement breaking at a fixed amplification"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Definition 3.1 of Devendra, Mallick and Sumesh requires a complex-linear map and a positive k-fold left amplification. Every positive semidefinite input to that amplification must give a finite sum of Kronecker products of positive semidefinite factors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-choicongruences-iskeb-of-choi-congruences"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.isKEB_of_choi_congruences"),
                H("Choi compressions suffice for entanglement breaking"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A rank-one positive input amplifies to a rectangular local congruence of the input-first Choi matrix. A positive semidefinite input is a finite sum of these rank-one inputs. Separability is preserved under their sum."))),
                DescribeRole.Theorem))));
}
