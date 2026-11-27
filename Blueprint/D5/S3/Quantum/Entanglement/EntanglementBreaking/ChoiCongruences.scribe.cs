using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class ChoiCongruencesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Resource/devendra2023mapping");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular Choi congruences and the k-entanglement-breaking condition.",
        H("Choi congruences and entanglement breaking"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-choicongruences-inputchoi"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi"),
                H("Input-first Choi matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The entry with row (i, u) and column (j, v) is the (u, v) entry of the image of the (i, j) matrix unit. This corresponds to the input-first convention in Section 2 of Devendra, Mallick and Sumesh (2023)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-choicongruences-iskeb"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.IsKEB"),
                H("Entanglement breaking at a fixed amplification"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Definition 3.1 of Devendra, Mallick and Sumesh requires a complex-linear map and a positive k-fold left amplification. Every positive semidefinite input to that amplification must give a finite sum of Kronecker products of positive semidefinite factors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-choicongruences-iskeb-of-choi-congruences"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.isKEB_of_choi_congruences"),
                H("Choi compressions suffice for entanglement breaking"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A rank-one positive input amplifies to a rectangular local congruence of the input-first Choi matrix. A positive semidefinite input is a finite sum of these rank-one inputs. Separability is preserved under their sum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-choicongruences-frominputchoi"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.fromInputChoi"),
                H("From input choi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Reindex the supplied input-first matrix by swapping the two factors and apply the inverse Choi map."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-choicongruences-inputchoi-frominputchoi"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.inputChoi_fromInputChoi"),
                H("Input choi from input choi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Starting from any input-first matrix, inverse Choi conversion followed by input-first Choi conversion gives back the same matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-choicongruences-amplify"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify"),
                H("Amplify"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Tensor the identity map on k by k complex matrices with the given map, with the ancilla as the first factor."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-choicongruences-amplify-apply"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_apply"),
                H("Amplify apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The amplified entry is the sum over input indices i and j of the Choi entry times the corresponding input block entry."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-choicongruences-amplify-vecmulvec"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.amplify_vecMulVec"),
                H("Amplify vec mul vec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The positive rank-one matrix of a vector with coefficient matrix A amplifies to the local congruence of the Choi matrix by A tensor the output identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-choicongruences-separable-local-congruence"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences.separable_local_congruence"),
                H("Separable local congruence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A rectangular local congruence on the first factor preserves separability. It replaces every first positive factor P by A P A*."))),
                DescribeRole.Theorem))));
}
