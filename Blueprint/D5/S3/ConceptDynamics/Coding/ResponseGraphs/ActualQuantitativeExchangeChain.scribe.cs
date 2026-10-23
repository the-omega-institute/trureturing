using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseGraphs;

internal sealed class ActualQuantitativeExchangeChainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same actual numbered-edge span gives all four original quantitative SSE branches.",
        H("Independent actual forgetting depths"),
        Blocks(
            Paragraph(Text("Let n, k and q be positive natural numbers. Let A, B and C be essential square natural matrices of these orders. The inputs are I : ActualIncoming C A and J : ActualIncoming C.transpose B.transpose. Both maps use the same actual numbered C-edges, with edge reversal retaining their numbers. Let dL and dR be the least natural depths at which the two state lifts forget their terminal boundary state; zero is included. No CompatibleCertificate, positive-depth premise, rectangular factorization or response identity is assumed.")),
            Describe.Lean(DescribeId.Create("actualquantitativeexchangechain-full52"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuantitativeExchangeChain.full_original_52"),
                H("The original quantitative chain"),
                StatementSource.FromAuthor(FormulaDsl.Disp(
                    Call("ExistsControlledChainWithLengthBound",Id("A"),Id("B"),Id("q"),
                        Call("max",Call("max",Num(1),Id("dL")),
                            Call("max",Id("dR"),Call("sub",Call("add",Id("dL"),Id("dR")),Num(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist natural M and ell with a Nonempty ControlledChain q M A B ell and ell at most max(max(1,dL),max(dR,dL+dR-1)). ControlledChain retains every natural rectangular factor and square node; every node has order at most q and is essential. M is an auxiliary uniform entry bound chosen from the actual finite factors, not a hypothesis. ControlledChain.erase yields the ordinary ExchangeChain from literal A to literal B."))), DescribeRole.Theorem),
            Paragraph(Text("The actual source-class count identifies each response matrix with IL C SL under any numbering and any section. At depth one the same actual counting formula gives equal C columns on the left classes and equal C rows on the right classes. The existing first_response_diamond therefore gives a single exchange between those same first response matrices. The response controls derive outgoing witnesses from actual C-edges using unique lifting, preserve essentiality and bound quotient orders by q.")),
            Paragraph(Text("If both depths are positive, reverse the left controlled tail from dL to one, join the actual diamond, and follow the transposed right controlled tail from one to dR. The length is (dL-1)+1+(dR-1)=dL+dR-1. If only dL is zero, use the complete right tail of length dR; if only dR is zero, use the reversed complete left tail of length dL. At depth zero the response quotient is the equality quotient and its matrix is C. The terminal response-matrix theorem also applies at zero, so the zero-depth endpoint is a reindexing of C. With both depths zero, reindex the single exchange C=C*1=1*C to A and B. The two endpoint numberings are absorbed simultaneously in an existing exchange, including a one-step chain.")),
            Paragraph(Text("This is the arbitrary-span scope of section 5.2 in the original Recursive Relational Observation SFT source (archive revision 79db42486051ece852b5ee8d567ceb3427c275b3), with its zero branches and same-object conditions. It does not infer an arbitrary-span certificate from the compatible positive-lag setting of Bilich, Dor-On and Ruiz. The classical SSE literature supplies context, not an external citation for the precise combined length and order bounds stated here. No optimality or global novelty claim is made."))
        )));
}
