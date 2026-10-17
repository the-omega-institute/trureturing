using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseGraphs;

internal sealed class OriginalResponseGraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResponseGraphs/OriginalResponseGraph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-table conjugacy on the original legal histories has a finite response presentation with two actual projections and a counted adjacency matrix.",
        H("Centered response histories and their numbered edges"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-response-presentation"),
                DeclarationHandle.Create(Prefix + "response_reduction"),
                H("Two projections of one essential finite graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G be a directed multigraph with finite vertex and edge types, decidable vertex equality and a discrete edge topology. The four radii a,b,c,d are arbitrary natural numbers, including zero. TablePair supplies f on legal words of length a+b+1 and g on legal words of length c+d+1. SameTableConjugacy supplies the original mutually inverse continuous maps on History G, their exact table equations and their commutation with the original unit left shift. Essential G supplies actual incoming and outgoing edges at every vertex.")),
                    Paragraph(Text("A response vertex is a legal input word of length a+b+1. A response edge stores a legal word of length a+b+2 and its literal f response on the length a+b+1 prefix. The source is that prefix and the target is the length a+b+1 suffix. The edge subtype retains distinct parallel input words. The input projection takes coordinate a of each response word; its vertex projection takes the source of coordinate a. The output projection takes the stored response; its vertex projection takes the source of f at the vertex word. The seam obtained from the supplied conjugacy proves both output endpoint equations.")),
                    Paragraph(Text("The lift at time i stores the original input window from i-a through i+b+1. Its inverse is the centered input projection. The overlap induction reconstructs every coordinate of every arbitrary legal response history, proving that there are no additional response histories outside the lift image. These maps are inverse homeomorphisms. The output homeomorphism has inverse y mapped to the lift of the supplied backward image of y. On every response history z, the output equals the supplied forward map of the input projection. All three history maps commute with the original unit shift, with no time correction.")),
                    Paragraph(Text("The inverse table applies g at every position of an output word from i-a-c through i+b+d+1, including both endpoints. This recovers the whole input word of length a+b+2 and then its actual response edge. Essentiality of the response graph follows by realizing each positive vertex word in an original history and taking its adjacent lifted edges. Empty carriers remain in scope. The conclusion also identifies the response-edge cardinality with the cardinality of all legal input words of length a+b+2."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("response-output-synchronization"),
                DeclarationHandle.Create(Prefix + "output_synchronizes"),
                H("A literal output interval determines the whole response edge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any two legal response histories and any integer i, equality of every output edge at integer times from i-a-c through i+b+d+1 implies equality of their complete response edges at i. The recovered object includes both the input word and its response label. This uses the finite inverse-table recovery on arbitrary response histories, rather than assuming that either history was supplied as a lift."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-response-label"),
                DeclarationHandle.Create(Prefix + "finite_recovery_label"),
                H("Every legal output word has the stated recovered label"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every legal output word of length (a+c)+(b+d+1)+1, the output label of its recovered response edge is exactly coordinate a+c of that word. The word need not be presented as an image window. Positive-word realization places it in an actual history; the supplied inverse homeomorphism and response recovery prove the label identity. Under the counted edge equivalence, the label identity gives the final finite-word clause of numbered_response_reduction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("numbered-original-response"),
                DeclarationHandle.Create(Prefix + "numbered_response_reduction"),
                H("The actual counted matrix retains every endpoint fibre"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Number every response vertex by Fintype.equivFin in its actual vertex-to-Fin orientation. At a pair of numbered vertices, the adjacency entry is the cardinality of the subtype of actual response edges with exactly those endpoints. No vertex or zero entry is removed. A counted edge is decoded by inverting equivFin on its actual endpoint fibre and then forgetting that fibre's index. The inverse encoding retains every parallel edge number. A zero entry is equivalent to the absence of any original response edge in that fibre, including when the whole vertex type is empty.")),
                    Paragraph(Text("The edge equivalence gives a homeomorphism from response histories to the existing CountedMatrixOverlap.Path subtype. Composing with the input and output homeomorphisms produces numberedLift and numberedOutput on the original History G. The counted graph is essential, numberedOutput after numberedLift is the supplied forward map, and the output at every integer time is the literal output label of the decoded numbered edge. The unit shift equations hold on every counted path and original history. The same inclusive inverse window recovers the actual counted edge, and every legal finite output word has the same central-label law after counted decoding.")),
                    Paragraph(Text("This construction supplies a finite response presentation and its counted numbering. It supplies no elementary state-splitting factorization, original-h arithmetic identity, literal Fix(T6) factorization, period-six sufficiency or minimum-six theorem. The derivation uses EssentialWordRealization, FiniteWindowTableCriterion and the existing counted Path carrier. The square and response-quotient matrices in CompatibleResponseForgetting concern different input data; no such certificate is assumed here. The construction makes no claim of literature novelty."))),
                DescribeRole.Theorem))));
}
