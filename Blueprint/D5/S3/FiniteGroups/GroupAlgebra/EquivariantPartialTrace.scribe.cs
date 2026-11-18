using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class EquivariantPartialTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial trace preserves equivariance and transports trace-zero pairings through an actual tensor product over an arbitrary field.",
        H("Equivariant partial trace without dimension division"),
        Blocks(
            Paragraph(Text("Let K be any field, G any group, and A, B, C K-vector spaces in independent universes. The linear construction requires A and C finite-dimensional; B is also finite-dimensional in the trace-pairing statements. The right partial trace contracts the C-endomorphism factor in Hom(A tensor C, B tensor C) using its ordinary trace. It is not divided by dim C, so positive characteristic and dimensions vanishing in K are retained.")),
            Describe.Lean(
                DescribeId.Create("partial-trace-pure-map"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_map"),
                H("Contract a pure tensor map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For f:A->B and t:C->C, the contraction of f tensor t is trace(t) times f. The implementation uses the actual hom-tensor-hom linear equivalence and the usual linear trace."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-trace-pairing-identity"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_comp_map_eq_trace_rightPartialTrace"),
                H("Transfer the trace pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F:A tensor C->B tensor C and d:B->A, trace on B tensor C of F composed with d tensor id_C equals trace on B of the right partial trace of F composed with d. The proof expands the actual tensor of hom spaces and uses the tensor-product trace identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-trace-conjugation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.rightPartialTrace_conjugate"),
                H("Move the outer maps through the contraction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If c' composed with c is id_C, contracting (b tensor c) composed with F composed with (a tensor c') gives b composed with the contraction of F composed with a. Cyclicity of trace removes the C-maps. Applied to a group element and its inverse, this identity proves that the partial trace of an intertwiner is itself an intertwiner; equivariance is derived rather than assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-trace-zero-pairing-tensor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace.trace_pairing_zero_rTensor"),
                H("Tensor a map with vanishing trace pairings"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose d:A->B is equivariant and trace(g composed with d)=0 for every equivariant g:B->A. Then, for every equivariant F:B tensor C->A tensor C, trace(F composed with d tensor id_C)=0. Contracting F provides the required equivariant return map. This is the bridge used when the first binary obstruction occurs inside a triple tensor."))),
                DescribeRole.Theorem),
            Paragraph(Text("The general mechanism is classical: negligible morphisms form a tensor ideal, as in Pavel Etingof and Victor Ostrik, On semisimplification of tensor categories, arXiv:1801.04409, Lemma 2.3, PDF page 4. The concrete Lean proof here constructs the contraction and its equivariance. The same paper, PDF page 6, distinguishes negligible morphisms from maps factoring through negligible objects. Accordingly, vanishing trace pairings are used only for an obstruction; they do not replace the original M-relative factorization ideal in the Elmer--Kadr applications. No novelty claim is made for the partial-trace mechanism.")))));
}
