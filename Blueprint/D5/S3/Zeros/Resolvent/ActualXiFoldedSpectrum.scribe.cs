using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class ActualXiFoldedSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual reflection-folded xi spectrum.",
        H("Actual reflection-folded xi spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualxifoldedspectrum"),
                DeclarationHandle.Create("D5/S3/Zeros/Resolvent/ActualXiFoldedSpectrum.node_large_finite"),
                H("Actual reflection-folded xi spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("PositiveZero is the subtype of the original canonical distinct-zero enumeration whose imaginary part is positive. Reflection rho maps to 1-rho and selects exactly one sign of height; analytic multiplicity remains a positive natural weight. The complex node is gamma(rho) to the power minus two, equivalently minus one divided by (rho minus one half) squared. Its weight is twice the original multiplicity times the normalized reciprocal rho(1-rho) times that node. No off-line orbit is removed.")),
                    Paragraph(Text("The restricted reflection-after-conjugation permutation is an involution and conjugates both node and weight, while preserving multiplicity. Equality of folded nodes forces equality or negation of gamma; positive height excludes negation, so distinct representatives give distinct nodes. Reality is equivalent to the original zero having real part one half. On those real nodes the node and weight are strictly positive. All nodes and weights are nonzero, the node norms lie strictly between zero and one, and the complete absolute weight sum converges.")),
                    Paragraph(Text("For every positive epsilon the indices with node norm at least epsilon form a finite set, by the actual zero source spectral-ball finiteness. This is about distinct zeros, not occurrence fibers: multiplicity changes the weights without multiplying the number of off-line conjugate node pairs. These are classical coordinate and convergence facts; no ordinary originality or Riemann-hypothesis conclusion is asserted.")))))));
}
