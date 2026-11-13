using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuTransitionSpanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualZhuTransitionSpan", H("Full source transition span"), Blocks(
            Paragraph(Text("The carrier and literal circle span are unchanged. The lattice is arbitrary positive-definite integral even, including rank zero and zero charge. Mature source: Dong, Li and Mason, Certain associative algebras similar to U(sl2) and Zhu's algebra A(V_L), DOI 10.1006/jabr.1997.7112, https://arxiv.org/html/q-alg/9605032v1, Theorem 3.4 and Remark 2.11. Native energy, oscillator, source support and inverse Gram suppliers are reused. Lagrange interpolation is supplied by pinned Mathlib under Apache-2.0. These are components of the finite source-span and joint-faithfulness consumer; no independent mathematical novelty or physical completion is asserted.")),
            Describe.Lean(
                DescribeId.Create("actualzhutransitionspan-source-transition-span"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/ActualZhuTransitionSpan.source_transition_span"), H("The entire literal quotient is spanned by minimum transitions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transitions are E_(gammaOut-gammaIn) times the source projector at rep(c) plus G gammaIn. Both charges range over the complete attained-minimum fiber in every discriminant class. First all-alpha elimination identifies surviving input weights. The native charged right-support relation then kills each transition unless its output has exactly the same minimum energy. Finally quotient-map surjectivity, finite charge support, the compiled full oscillator normal form and the source sum-one decomposition prove spanning of Q itself. This argument precedes every bottom action and assumes no source span, representation kernel identity, semisimplicity or rationality."))), DescribeRole.Theorem))));
}
