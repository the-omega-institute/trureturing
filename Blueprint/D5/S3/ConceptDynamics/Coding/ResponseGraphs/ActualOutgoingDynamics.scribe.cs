using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseGraphs;

internal sealed class ActualOutgoingDynamicsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual path reversal transports chronological outgoing observations.",
        H("Chronological dynamics of actual outgoing lifts"),
        Blocks(
            Describe.Lean(DescribeId.Create("actualoutgoingdynamics-rholift"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoLift"),
                H("Reverse each actual outgoing edge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any natural n, matrix A : CountMat n n, type Q, onto p : Q → Fin n and maps rho_b from the source fiber of every actual numbered A-edge b to its target fiber, rhoLift p hp rho is an incoming lift of A.transpose. Its projection is the original p. The reversed edge with endpoints b.target,b.source retains b.number and acts by the original rho_b. No finiteness, essentiality or forgetting is assumed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualoutgoingdynamics-lift-append"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.lift_append"),
                H("Appending one edge composes actual lifts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every incoming lift L, endpoint-indexed path alpha from i to j, actual edge a from j to k and terminal state v above k, lifting appendPath alpha a at v equals lifting alpha at the lifted value of a. This directly reuses concatenate_paths and the original numbered-word injectivity and append-word suppliers; there is no second path-concatenation proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualoutgoingdynamics-rhopath"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rhoPath"),
                H("Chronological outgoing path evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the original outgoing data p,hp,rho on A, rhoPath evaluates the empty path by identity. For a first actual edge b followed by a tail, it applies rho_b to the initial state and then evaluates the tail. Consequently a chronological path b1…bd acts by rho_bd composed through rho_b1 on its entire source fiber, with every edge number and both endpoints retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualoutgoingdynamics-chronological-rho"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.chronological_rho"),
                H("Reversal computes the original chronological path"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original outgoing datum p,hp,rho, natural length d, endpoint-indexed path beta in A from i to j, and state u above i, (rhoLift p hp rho).liftPath (reverseFinitePath beta) u equals rhoPath p hp rho beta u as elements of the original terminal fiber above j. The path induction uses lift_append, so the reversal includes the order of all edges as well as their directions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualoutgoingdynamics-reverse-reverse"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.reverse_reverse"),
                H("Reversing an actual finite path twice recovers it"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any matrix A, natural d and endpoint-indexed actual path alpha : FinitePath A d i j, reverseFinitePath (reverseFinitePath alpha) equals alpha. The proof reuses reverse_word, the original word_endpoint_injective and the involution of numbered edge reversal. Empty paths are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualoutgoingdynamics-rho-response-paths"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualOutgoingDynamics.rho_response_paths"),
                H("Responses are the original chronological observations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every p,hp,rho, natural d and states u,v, the d-response of rhoLift p hp rho holds exactly when p u = p v and every actual length-d path beta in the original graph A with that initial vertex gives equal rhoPath values at u and v. The two directions use chronological_rho and double reversal. Thus the response kernel is identified with the outgoing chronological observations on the same original graph, including d=0; a transpose matrix identity is not its premise."))), DescribeRole.Theorem)
        )));
}
