using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuRightIdealDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualZhuRightIdeal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right-argument O stability of original Zhu star",
        H("Right-argument O stability of original Zhu star"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualzhurightideal-star-right-mem-zhuo"),
                DeclarationHandle.Create(Prefix + "star_right_mem_zhuO"),
                H("Original Zhu star preserves O in its right argument"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For positive-definite real Gram matrix, all u and o of the complete original Carrier(D), and membership o in the literal ActualZhuFinite.zhuO(D), star(D,u,o) belongs to that same submodule. Native nonnegative-product finite support gives one finite commutator index set valid for all modes. On homogeneous u and a, the expansion of u star circle(a,b) splits into a sum of original circles and commutator corrections. A correction state u_s a has energy K+M-s-1; negative energy forces it to zero. For nonnegative energy, zhu_right_binom rewrites its entire weighted correction into a finite combination of higher circles with orders t+1. Finite original energy decomposition in u and span induction in o conclude the theorem."))),
                DescribeRole.Theorem),
            Paragraph(Text("Source-faithful native port of Fedor K. Popov, Lean_VOA, commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean, ZhuRingResidue.lean and ZhuRightIdeal.lean; Apache-2.0, with classical Zhu/Frenkel-Zhu attribution. The local carrier, fields, grading, derivative, commutator and O-space are the existing actual lattice construction. The local port is not independent mathematical novelty.")),
            Paragraph(Text("This theorem establishes star(u,o) in the same full O for arbitrary original u and o in O under positive definiteness. Opposite-argument stability star(o,u) in O and associator membership (u star v) star w - u star (v star w) in O are beyond this result. A bilinear product on the quotient requires both argument stabilities; an associative quotient Ring or Algebra requires further structure. Analytic CFT, fusion, anomaly, string theory and AdS/CFT remain outside this result.")),
            Paragraph(Text("Four-slot escape registration for star_right_mem_zhuO is unfinished: no faithful enrolled original-statement reconstruction, scoped readout, law bridge, whole-family variation, sensitivity, actual observational dependence and source-selection/realization evidence is supplied. https://github.com/the-omega-institute/trureturing/issues/28732 tracks this product-chain audit. Neither compilation nor the linked issue establishes declared_validated registration.")))));
}
