using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceBPZ;

internal sealed class ThetaChargeIntertwinerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeIntertwiner.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit residue-one restriction and theta reconstruction classify dihedral intertwiners with zero neutral block.",
        H("Reconstructing the Paired Charge Intertwiner"),
        Blocks(
            Paragraph(Text(
                "Let D and E be independent positive-definite integral even lattice data, ellD and ellE additive charge maps to ZMod 3, and m,n arbitrary integers. Use one common unit-valued phase whose value at residue one is not one. The source and target are the existing gradeChargeDihedralRepresentation on grade D m and grade E n. There is no surjectivity, equal-rank, equal-lattice, nonempty-sector, or nonnegative-grade hypothesis.")),
            Definition("gradeChargeResidueProjection", "Projection on the actual coefficient sector",
                "For each r, P_D,r is transported coefficient filtering: apply gradeCoeffEquiv D m, retain exactly the energy-fiber labels a with ellD(a.charge)=r using Finsupp.restrictDom, and return through the inverse coordinate equivalence. The output is the actual gradeChargeResidue subtype. It is the identity on residue r and zero on the other two residues. In particular every x is P_D,0 x + P_D,1 x + P_D,2 x, with inclusions understood."),
            Definition("gradeChargeIntertwinerH0", "The zero-neutral intertwiner submodule",
                "H0 is the complex submodule of Representation.IntertwiningMap rho sigma consisting of T such that T x=0 for every x in the source residue-zero subspace. This is a condition on the actual full-grade map, and it is preserved under addition and complex scalar multiplication."),
            Paragraph(Text(
                "The chargePhaseScalar hom laws and chargePhaseScalar_eq_one_iff make the scalar phase injective on ZMod 3: equality at r and s implies phase(r-s)=1, hence r=s. A vector supported in residue r is an eigenvector of the generator rotation with eigenvalue phase(r). Applying the intertwining equation and comparing every target coefficient forces all coefficients outside residue r to vanish. Thus restriction of an actual intertwiner has the required residue-one codomain.")),
            Definition("gradeChargeIntertwinerRestrict", "The forward map is literal restriction",
                "For T in H0 and x in gradeChargeResidue D ellD m 1, restriction sends x to T x, equipped with its proved membership in gradeChargeResidue E ellE n 1. No choice of bases or dimension comparison selects this map."),
            Definition("gradeChargeIntertwinerFromResidue", "The inverse reconstructs the full map",
                "For any complex-linear B from source residue one to target residue one, define F_B(x) = incl_E,1(B(P_D,1 x)) + theta_E(incl_E,1(B(P_D,1(theta_D x)))). The same formula defines a complex-linear map in x and depends complex-linearly on B. The code proves its rotation and theta commutation and constructs the actual Representation.IntertwiningMap, with F_B zero on the neutral source subspace."),
            Law("gradeChargeIntertwinerFromResidue_apply", "Actual reconstruction computation",
                "For every full source-grade vector x, evaluation of gradeChargeIntertwinerFromResidue B is exactly the displayed two-term formula, using the source gradeTheta D m, target gradeTheta E n, and the genuine source coefficient projection."),
            Paragraph(Text(
                "Theta maps residue r to -r by the existing gradeTheta_mem_gradeChargeResidue_neg theorem. The first reconstruction term has target residue one; the second has target residue two. For rotation i they acquire the scalars phase(i) and phase(-i), respectively. The source identity theta_D R_D(i) theta_D=R_D(-i), together with coefficient projection, gives precisely the same two scalars before applying F_B. Theta commutation follows directly from theta_D squared and theta_E squared being identities. The rotation and reflection constructors of the six-element group then give all intertwining equations in the direction F_B composed with rho(g) equals sigma(g) composed with F_B.")),
            Law("gradeChargeIntertwinerRestrict_fromResidue", "Restriction recovers B",
                "For x in source residue one, P_D,1 x=x and P_D,1(theta_D x)=0, since theta_D x has residue two. The reconstructed map therefore takes x to B x, so restriction(F_B)=B as actual complex-linear maps."),
            Law("gradeChargeIntertwinerFromResidue_restrict", "Reconstruction recovers T",
                "For T in H0, reconstructing its restriction gives T(P_D,1 x) + theta_E T(P_D,1(theta_D x)). Theta commutation changes the second term to T(theta_D(P_D,1(theta_D x)))=T(P_D,2 x). The coefficient decomposition and T(P_D,0 x)=0 yield F_(restriction(T))(x)=T x for every x."),
            Definition("gradeChargeIntertwinerEquiv", "Specified complex-linear equivalence",
                "The restriction map and the explicit reconstruction, with the two inverse identities above, form H0 equivalent over the complex numbers to the space of all complex-linear maps from gradeChargeResidue D ellD m 1 to gradeChargeResidue E ellE n 1. This equivalence computes the intertwiner itself. It does not use an existence theorem based on equality of dimensions."),
            Paragraph(Text(
                "The construction includes degenerate sectors. If ellD is the zero charge map, source residue one is zero and every source-grade vector belongs to residue zero. Consequently both the arbitrary residue-one linear data and every member of H0 are zero. The displayed reconstruction sends zero data to the zero map, and the same restriction/reconstruction equivalence still applies, without a nonempty-sector hypothesis.")),
            Paragraph(Text(
                "This construction isolates the paired nonzero charge sector and explains why its residue-two action is forced by its residue-one action. The zero-neutral condition is essential to uniqueness: an additional neutral block is outside this increment. The existing theta-only plus/minus block equivalence and generic character averaging do not supply the coefficient extension constructed here. No counting corollary, full neutral sign decomposition, analytic completion, or literature novelty claim is included."))
        ), []));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("theta-charge-intertwiner-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Law(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("theta-charge-intertwiner-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
