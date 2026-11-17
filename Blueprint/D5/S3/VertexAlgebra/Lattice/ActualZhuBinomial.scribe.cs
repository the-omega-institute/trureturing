using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuBinomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualZhuBinomial.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Zhu binomial collapse",
        H("Weighted Zhu binomial collapse"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualzhubinomial-zhu-right-binom"),
                DeclarationHandle.Create(Prefix + "zhu_right_binom"),
                H("The weighted commutator coefficient collapses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For all natural K, M, s and integer mode m, the sum over p of C(K,p) C(M,m+3+s-p) C(p-1,s) equals the alternating sum over t from 0 to s of (-1)^t C(K,s-t) C(K+M-s+t,m+3+t). The integer-lower coefficient is zero only for negative lower index; a negative upper index retains Ring.choose. Vandermonde, the alternating top row and trinomial revision prove the identity. This scalar identity is consumed by the original-carrier right-argument O stability proof."))),
                DescribeRole.Theorem),
            Paragraph(Text("Source-faithful native port of Fedor K. Popov, Lean_VOA, commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean, ZhuRingResidue.lean and ZhuRightIdeal.lean; Apache-2.0, with classical Zhu/Frenkel-Zhu attribution. The local carrier, fields, grading, derivative, commutator and O-space are the existing actual lattice construction. The local port is not independent mathematical novelty.")),
            Paragraph(Text("The consuming chain establishes star(u,o) in the same full O for arbitrary original u and o in O under positive definiteness. Opposite-argument stability star(o,u) in O and associator membership (u star v) star w - u star (v star w) in O are beyond this result. A bilinear product on the quotient requires both argument stabilities; an associative quotient Ring or Algebra requires further structure. Analytic CFT, fusion, anomaly, string theory and AdS/CFT remain outside this result.")),
            Paragraph(Text("Four-slot escape registration for zhu_right_binom is unfinished: no faithful enrolled original-statement reconstruction, scoped readout, law bridge, whole-family variation, sensitivity, actual observational dependence and source-selection/realization evidence is supplied. https://github.com/the-omega-institute/trureturing/issues/28732 tracks this product-chain audit. Neither compilation nor the linked issue establishes declared_validated registration.")))));
}
