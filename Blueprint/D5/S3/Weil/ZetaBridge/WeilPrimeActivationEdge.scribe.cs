using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilPrimeActivationEdgeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original prime-activation edge overlap has a rank-one first-order term; the already-owned even zero-trace stencil suppresses both its edge mass and cross-edge pairing to fifth order.",
        H("Prime Activation Edge"),
        Blocks(
            Describe.Lean(DescribeId.Create("cosine-prime-edge-remainder"),
                DeclarationHandle.Create(Owner + "cosine_prime_edge_remainder"),
                H("Actual cosine edge overlap and rank-one leading term"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real u,v and h>=0, bound the difference between integral_0^h cos(u*t)cos(v*(h-t)) and h by (u^2+v^2)h^3/6. Continuous integrands and the exact quadratic polynomial integral are used. This is the actual low-mode overlap when a compressed prime shift enters through the two window endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-stencil-edge"),
                DeclarationHandle.Create(Owner + "evenStencilEdge"),
                H("Boundary profile of the existing zero-trace stencil"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite complex sum uses cos(pi*n*t)-1, the edge profile of V_n+V_(-n)-2V_0 after the original unitary dilation, with a fixed factor sqrt(2). Zero trace is structural in this particular trial. It is not imposed on the actual Weil candidate or on an unknown eigenfunction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-stencil-edge-fifth-order"),
                DeclarationHandle.Create(Owner + "even_stencil_edge_fifth_order"),
                H("Complete edge mass and cross-edge correlation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let K=sum_n norm(v_n)*(pi*n)^2. The theorem derives integrability and bounds the actual integral of norm(edge(t))^2 by K^2*h^5/20 and the norm of integral conj(edge(t))*edge(h-t) by K^2*h^5/120. Coefficients remain complex and all mixed terms are retained before the bound. The proof uses the actual cosine defect and the exact t^2*(h-t)^2 integral, not a supplied boundary-decay assumption.")),
                    Paragraph(Text("The associated numerical increment independently certifies the full candidate-orthogonal Weil form throughout |a-log(3)/2|<=10^-8, retaining prime 3 on its active side, the complete infinite Fourier complement and all boundary moments. Its interval matrix identification, Schur completion and spectral consequence remain paper/computer-assisted bridges. The fifth-order trial estimate explains one special low-block mechanism; it is not used to set the genuine candidate's endpoint to zero. Lean elaboration, Scribe emission and a transitive axiom report have not run."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/WeilEvenDualStencil"))]));
}
