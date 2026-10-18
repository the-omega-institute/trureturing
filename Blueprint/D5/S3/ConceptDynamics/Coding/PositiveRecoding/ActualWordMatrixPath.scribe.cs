using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class ActualWordMatrixPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite graph words give chronological rectangular RS paths and exact scalar-extended endpoint maps.",
        H("Actual finite graph words give chronological rectangular RS paths and exact scalar-extended endpoint maps"),
        Blocks(
            Paragraph(Text("This dictionary changes representations while preserving the full endpoint map. It works over GyrationDyadic using rectangular ROW factors; the full integer history and the independently constructed beam action remain the objects to be compared downstream.")),
            Paragraph(Text("ActualWordRelabelAssembly supplies dictionary_residue, which word_rebased uses to connect the matrix-path weight to the actual periodic action.")),
            Describe.Lean(
                DescribeId.Create("actualwordmatrixpath-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.relabel_time"),
                H("Adjacency intertwining from the actual edge bijection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite vertex types V,W and finite edge types E,J with the stated vertex equality decisions, Relabel G H retains both vertex and edge bijections. relabel_adjacency is obtained from the existing edge-count transport. reindex r.vertex sends a vertex coefficient z to z composed with r.vertex inverse. relabel_time derives its intertwining with the adjacency time maps by reindexing the full vertex sum. No adjacency conjugacy is postulated and parallel-edge identities are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualwordmatrixpath-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.positiveEdge"),
                H("Rectangular RS factors in chronological row order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For R : CountMat n m and S : CountMat m n, counts extends coefficients to GyrationDyadic and counts_mul preserves multiplication. positiveEdge goes from countedBased(R*S) to countedBased(S*R), with forward map (counts R).toLinearMapRight' and backward map (counts S).toLinearMapRight'. Thus s.comp r is old time and r.comp s is new time. The conventional COLUMN matrix of the forward map is transpose R; its ROW matrix is R. rows(g.comp f)=rows(f)*rows(g), so row factors multiply in chronological order. All zero ranks, zero entries and singular intermediates are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualwordmatrixpath-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.vertex_matrix"),
                H("Use precisely the existing history chart basis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("presentationBasis F is Pi.basisFun transported by reindex of the vertex bijection of ActualPositiveWordPeriodicCochain.chart F. vertex F stores the actual graph adjacency time in that basis. vertex_matrix derives its ROW matrix as counts of ActualPositiveWordPeriodicCochain.matrix F from relabel_time and faithful rows_transport. It does not assert equality with a fixed signed COLUMN matrix used in the arithmetic character."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualwordmatrixpath-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.dictionary_forward"),
                H("Every actual positive word has its original endpoint map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("dictionary maps a relabel leaf to one RS edge and a positive leaf to three: relabelEdge old.symm, positiveEdge R S, relabelEdge next. length counts these RS edges, not Word.letters. Composition appends paths over the identical intermediate Based object. Path.append_forward derives forward(v after u)=v.forward.comp u.forward, and dictionary_forward identifies the full path map with endpointMap w. For a positive leaf this is next reindex composed with R acting on old inverse coefficients; both graph chart arrows remain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualwordmatrixpath-5"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath.endpointMap_cast"),
                H("Compare the actual integer and dyadic maps before colimits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary Word F H and every integer vertex coefficient function z : F.V to integers, scalar extension of PositiveWordBeamTransport.endpointMap w z equals endpointMap w applied to the same coefficientwise embedded z, at every actual vertex of H. Induction uses the literal positive factors and constructor order. The preserved original application applies this equality at actual integer basis vectors to identify the finite coefficient matrix of the native endpoint action. It does not infer equality from an injective colimit or from a finite-period action."))),
                DescribeRole.Theorem),
            Paragraph(Text("The matrix-coordinate identities keep the row convention explicit: the actual endpoint linear map is expressed in the chosen vertex bases before it is compared with periodic weights.")))));
}
