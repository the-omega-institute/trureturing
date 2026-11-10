using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeDualCosetZhuZeroModeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeDualCosetZhuZeroMode.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original dual-coset bottom and all-state zero modes",
        H("Original dual-coset bottom and all-state zero modes"),
        Blocks(
            Paragraph(Text("Let D be the original LatticeData: arbitrary natural rank, symmetric integral Gram matrix G and even diagonal. For the bottom and zero-mode action, assume the real Gram matrix is positive definite, take an integral charge beta and a rational vector mu with sum_j G(i,j) mu(j) = beta(i) for every i. The module is the original action(D,beta) on the full Carrier(D). No determinant-unit, positive-rank, norm-four or one-dimensional-bottom hypothesis is imposed.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhuzeromode-bottom"),
                DeclarationHandle.Create(Prefix + "Bottom"),
                H("The entire lowest rational energy fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bottom(D,mu,hD) is rationalGrade at h = chargeWeight(D,mu,minimizingCharge(D,mu,hD)). Here chargeWeight(gamma) is one half of (gamma+mu)^T G (gamma+mu). The minimizing charge specifies the energy value only; membership retains every original label of that energy. In particular, both minimizing charges of the rank-one Gram [2], mu=1/2 example remain in the same bottom, with the two independent actual eigenvectors supplied by LatticeDualCosetEnergyEndpoints.half_shift_actual_bottom_multiplicity. This abbreviation reuses the existing rationalGrade; it does not construct a smaller ground line."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhuzeromode-module-fulllaw"),
                DeclarationHandle.Create(Prefix + "module_fullLaw"),
                H("Original module Borcherds supplies the residue interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every D, integral beta and unrestricted original states a,b, module_borcherds gives the fullLaw for action(a), action(b) and r mapped to action(mu(a,r,b)), with shift zero. This interface conversion requires neither positive definiteness nor a rational dual vector. Its three finite-support witnesses are kept separate for moduleLeft, moduleFirst and moduleSecond; each is transported to its corresponding residue term. Ring.map_choose identifies the original integer binomial with complex Ring.choose, and the two separately finite right supports justify distributing finsum over subtraction. fullLaw is derived, never supplied as an extra hypothesis. Both homogeneous circle and star residue arguments in LatticeDualCosetZhuRepresentation use this interface to the original module Borcherds theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhuzeromode-high-mode-kills-bottom"),
                DeclarationHandle.Create(Prefix + "high_mode_kills_bottom"),
                H("Bottom-energy minimality kills high modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the stated positivity and dual-pairing conditions, for any integer weight k, integer mode n at least k, homogeneous original state a of weight k and any vector v in the full bottom, a_n v is zero. The actual mode-grade theorem puts a hypothetical nonzero output at rational energy h+k-n-1, strictly below h. The original moduleL eigenspace equivalence and point_spectrum_subset force that same eigenvalue to have energy h+m for a natural m. Injectivity of the rational-to-complex cast and the two order bounds give a contradiction. The proof reuses the original spectral and grading suppliers, without assuming a highest-weight annihilation law. Its consumers are both homogeneous residue arguments in the paired representation module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhuzeromode-zero-mode"),
                DeclarationHandle.Create(Prefix + "zeroMode"),
                H("A complex-linear zero mode on every original state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For each integer homogeneous grade k, the private consumed homogeneousZero uses the actual action coefficient k-1. Actual mode grading proves that this coefficient preserves the entire bottom since its energy shift is zero. Linearity in both state and bottom vector then gives a linear map from that grade into End_C(Bottom). DirectSum.toModule, composed with the original carrierEnergyDecomposition, assembles these maps into Carrier(D) ->_C End_C(Bottom). The original direct sum supplies finite homogeneous support; no field or state carrier is replaced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetzhuzeromode-zero-mode-homogeneous"),
                DeclarationHandle.Create(Prefix + "zeroMode_homogeneous"),
                H("Evaluation is the original coefficient in every integer degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer k, every original a in grade k and every bottom vector v, the underlying carrier vector of zeroMode(a)(v) is action(a) at coefficient k-1 applied to v. Negative and zero fused degrees are included. The circle and star residue arguments, the vacuum unit and representation_mk use this direct-sum evaluation law."))),
                DescribeRole.Theorem),
            Paragraph(Text("The source-faithful residue adaptation follows Fedor K. Popov's Lean_VOA, immutable commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, VOA/Modules/ZhuModule.lean and VOA/Modules/ZeroModeMult.lean, Apache-2.0. Copyright and license notices are retained in the paired Lean source and the library reference. This is literature-attested Zhu module mathematics combined with the native lattice fields, energy decomposition and module Borcherds suppliers, without a claim of independent literature novelty. LatticeDualCosetZhuRepresentation uses the full zero mode to descend the actual action to the literal Zhu quotient; ActualZhuJointFaithful then evaluates it on every tied minimum.")))));
}
