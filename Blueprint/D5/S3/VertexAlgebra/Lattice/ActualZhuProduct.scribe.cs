using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualZhuProduct.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-carrier Zhu star and higher circles",
        H("Original-carrier Zhu star and higher circles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualzhuproduct-star"),
                DeclarationHandle.Create(Prefix + "star"),
                H("Bilinear star on the complete original carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The original internal direct sum of all integer energy grades defines a linear map from Carrier(D) to its complex linear endomorphisms. On an integer grade p the finite formula uses p.toNat; under positive definiteness the negative grades contain only zero. No restricted vacuum-descendant carrier or additional decomposition choice is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhuproduct-star-homogeneous"),
                DeclarationHandle.Create(Prefix + "star_homogeneous"),
                H("Homogeneous finite star formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For any natural p, any original state a in energy grade p and any original state b, star(a,b) is the complete sum from j=0 through p of choose(p,j) times a_(j-1)b. This finite formula is used to expand the star product in the right-argument O stability proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhuproduct-highercircle"),
                DeclarationHandle.Create(Prefix + "higherCircle"),
                H("Full higher-circle family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The n-th higher circle of a state with natural weight M is the sum from i=0 through M+n of choose(M+n,i) times a_(i-2-n)b, on the same original carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhuproduct-highercircle-mem-zhuo"),
                DeclarationHandle.Create(Prefix + "higherCircle_mem_zhuO"),
                H("Higher circles belong to the same full O"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For positive-definite real Gram matrix, every natural n, homogeneous original a of natural energy M, and arbitrary original b, higherCircle(M,a,b,n) belongs to ActualZhuFinite.zhuO(D). The n=0 case is literally the existing full circle. The state derivative and actual translation grading prove the recursion (n+2) P(M,a,b,n+1) = P(M+1,T a,b,n) + (M+n+1) P(M,a,b,n); induction recovers the next residue by the nonzero scalar n+2."))),
                DescribeRole.Theorem),
            Paragraph(Text("Source-faithful native port of Fedor K. Popov, Lean_VOA, commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean, ZhuRingResidue.lean and ZhuRightIdeal.lean; Apache-2.0, with classical Zhu/Frenkel-Zhu attribution. The local carrier, fields, grading, derivative, commutator and O-space are the existing actual lattice construction. The local port is not independent mathematical novelty.")),
            Paragraph(Text("The consuming chain establishes star(u,o) in the same full O for arbitrary original u and o in O under positive definiteness. Opposite-argument stability star(o,u) in O and associator membership (u star v) star w - u star (v star w) in O are beyond this result. A bilinear product on the quotient requires both argument stabilities; an associative quotient Ring or Algebra requires further structure. Analytic CFT, fusion, anomaly, string theory and AdS/CFT remain outside this result.")),
            Paragraph(Text("Four-slot escape registration for star_homogeneous and higherCircle_mem_zhuO is unfinished: no faithful enrolled original-statement reconstruction, scoped readout, law bridge, whole-family variation, sensitivity, actual observational dependence and source-selection/realization evidence is supplied. https://github.com/the-omega-institute/trureturing/issues/28732 tracks this product-chain audit. Neither compilation nor the linked issue establishes declared_validated registration.")))));
}
