using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryOddPDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary odd p supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Odd P"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-p"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.p"),
                H("p"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized p statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-actual-p-entry"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.actual_p_entry"),
                H("actual p entry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual p entry statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-actual-p-multiply"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.actual_p_multiply"),
                H("actual p multiply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual p multiply statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-actual-p-inverse"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.actual_p_inverse"),
                H("actual p inverse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual p inverse statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-constraint"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.Constraint"),
                H("Constraint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual central law for the vector quotient and true central layer."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-actual-p-unitary-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.actual_p_unitary_iff"),
                H("actual p unitary iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual p unitary iff statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-actual-p-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.actual_p_upper"),
                H("actual p upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameterized actual p upper statement describes the actual unitary geometry or prescribed ordered-product construction. Its Lean telescope retains every field, rank, involution, input and equality hypothesis shown."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryoddp-actual-p-vector-lift"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryOddP.actual_p_vector_lift"),
                H("actual p vector lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every vector in the actual P/P(2) has a genuine unitary lift. Diagonal central coordinates use relative trace; all off-diagonal coupling is retained, including characteristic two."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}
