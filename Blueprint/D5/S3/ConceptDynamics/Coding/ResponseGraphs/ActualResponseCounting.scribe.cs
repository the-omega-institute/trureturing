using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseGraphs;

internal sealed class ActualResponseCountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual numbered-edge fibers identify response compression without a compatible certificate.",
        H("Actual lift fibers and response counts"),
        Blocks(
            Paragraph(Text("Let n and q be natural numbers, A an n by n natural matrix and C a q by q natural matrix. An ActualIncoming C A consists of a surjective vertex projection p, an actual numbered-edge readout preserving both endpoints, and a unique actual C-edge over every A-edge a with specified terminal state v over a.target. Its stateLift sends (a,v) to the source of this unique edge. Write L = I.stateLift and card for Nat.card in the displays. Neither essentiality nor forgetting is assumed in this module. Parallel edges retain their Fin(A i j) and Fin(C u v) numbers throughout.")),
            Paragraph(Text("For each natural depth d, responseReadout records the projected vertex and the complete responses to every actual length-d path. The response relation is its equality kernel. For a response class F and a terminal state v, incomingResponseFiber consists of actual numbered A-edges a for which the unique lift ending at v starts in F. Quotient representatives need not agree with any previously chosen vertex numbering.")),
            Describe.Lean(DescribeId.Create("actualresponsecounting-edge-equivalence"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualResponseCounting.responseEdgeEquiv"),
                H("The actual numbered-edge correspondence"),
                StatementSource.FromAuthor(FormulaDsl.Disp(Call("Equiv",
                    Call("incomingResponseFiber",Id("L"),Id("d"),Id("F"),Id("v")),
                    Call("ActualCEdgesEndingAtWithSourceClass",Id("C"),Id("v"),Id("F"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward map lifts the numbered A-edge to its specified terminal C-state; the reverse map reads the actual C-edge. The lift_read and unique fields prove the two inverse laws. The target type is precisely {c : Edge C | c.target = v and [c.source]_d = F}; it is not an unnumbered incidence relation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actualresponsecounting-count"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualResponseCounting.incoming_response_fiber_count"),
                H("Count by actual source states"),
                StatementSource.FromAuthor(FormulaDsl.Disp(Equal(
                    Call("card",Call("incomingResponseFiber",Id("L"),Id("d"),Id("F"),Id("v"))),
                    Call("sumSourceClassCounts",Id("C"),Id("d"),Id("F"),Id("v"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every I, d, F and v, the count is the sum over u : Fin q of C(u,v) when [u]_d = F and zero otherwise. The equivalence first retains the complete C-edge, then separates its source u and its number in Fin(C u v). Summing the cardinalities of those source fibers proves the formula, including depth zero and empty individual edge fibers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualresponsecounting-compression"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualResponseCounting.response_matrix_reindexed"),
                H("Literal incidence compression"),
                StatementSource.FromAuthor(FormulaDsl.Disp(Equal(
                    Call("reindex",Id("e"),Id("e"),Call("incomingResponseMatrix",Id("L"),Id("d"))),
                    Call("product",Id("IL"),Id("C"),Id("SL"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural r, equivalence e from the depth-d response quotient to Fin r, and section rep : Fin r to Fin q satisfying e([rep f]_d) = f, set IL(f,u) = 1[e([u]_d)=f] and SL(u,f) = 1[rep f=u]. The reindexed response matrix is literally IL C SL. The representative used by incomingResponseMatrix is Quotient.out; response monotonicity and incoming_response_fiber_card_step transport that representative to rep before the actual edge count is applied. Thus independently chosen representatives and numberings are covered."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actualresponsecounting-columns"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualResponseCounting.first_response_columns"),
                H("First responses determine actual columns"),
                StatementSource.FromAuthor(FormulaDsl.Disp(
                    All(Equal(Call("entry",Id("C"),Id("x"),Id("u")),
                        Call("entry",Id("C"),Id("x"),Id("v"))),
                        B("x",Call("Fin",Id("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The premise is I.stateLift.response 1 u v. At depth zero the response relation is equality. The source-class counting formula therefore recovers the individual C column, while the existing successor-fiber transport identifies its counts at u and v. Applying this result to J : ActualIncoming C.transpose B.transpose gives equality of the corresponding actual C rows."))), DescribeRole.Theorem),
            Paragraph(Text("For the original arbitrary-span construction, the same actual C is essential: left first-response classes give equal C columns and right first-response classes give equal C rows. The existing first_response_diamond then connects these same compressed response matrices. Generic response controls preserve essentiality and order at most q, and the terminal response-matrix theorem works at every forgetting depth, including zero. With two positive depths the two tails and one diamond have length dL+dR-1; with exactly one zero depth the other full tail suffices; with both zero the endpoints are permutation reindexings of C and a single exchange suffices. Simultaneous endpoint renumbering absorbs the permutations without extra steps. These statements describe the original target and its argument; this module proves the counting and first-response bridge, while a full controlled-chain conclusion requires its separate integration theorem.")),
            Paragraph(Text("The source context is the original Recursive Relational Observation SFT discussion, especially the actual merge count in section 3 and the diamond and four branches in section 5. The construction uses the existing ActualIncoming and response quotient interfaces. The classical splitting and SSE literature supplies context, including Williams (1973, with the 1974 erratum) and the symbolic dynamics chapter of Beal, Berstel, Eilers and Perrin (arXiv:1006.1265v3). No global novelty, optimality or matching external quantitative-bound claim is made."))
        )));

    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
