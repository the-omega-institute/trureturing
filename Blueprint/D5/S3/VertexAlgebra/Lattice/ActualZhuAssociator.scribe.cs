using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuAssociatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualZhuAssociator.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Zhu associator lies in the original circle span.",
        H("The original-carrier associator"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-zhu-associator-full"),
            DeclarationHandle.Create(Prefix + "associator_mem_zhuO"),
            H("Associator membership for all original states"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For every original lattice datum D with positive definite real Gram matrix, "
                    + "every original state u, every original state v, "
                    + "and every original state w, star(star(u,v),w)-star(u,star(v,w)) belongs to "
                    + "the literal ActualZhuFinite.zhuO D. The carrier includes all charges and all oscillator "
                    + "states, including rank zero. The O-space is the existing span of all homogeneous "
                    + "circle generators; no replacement kernel or smaller carrier is used.")),
                Paragraph(Text("Expanding the homogeneous products and applying the native "
                    + "LatticeAllStateReconstruction.stateField_iterate splits the left associated product "
                    + "into genuine U and V families in ActualZhuAssociatorExpansion. The supplied finite supports justify splitting and "
                    + "reindexing their finsums. Regularity bounds the nonnegative inner modes. "
                    + "The signed U and V binomial kernels identify the residual coefficients. "
                    + "ActualZhuMuIdentity.mu_identity expresses each coefficient tower as the finite sum "
                    + "of muCoeff times higherCircle. Each higherCircle belongs to the same O by "
                    + "ActualZhuProduct.higherCircle_mem_zhuO. Summing proves homogeneous membership. The original finite energy decomposition and bilinearity extend it to arbitrary u and v.")),
                Paragraph(Text("This is a source-faithful native port of Fedor K. Popov's Apache-2.0 "
                    + "VOA/Modules/ZhuAssociator.lean at "
                    + "https://github.com/Fedor-Popov/Lean_VOA/blob/013a799ca834a8a6b3afa8129e3e522025b3f45c/VOA/Modules/ZhuAssociator.lean. "
                    + "Its immutable SHA256 is 733725cca0c4ac72112b440392242d853378e35a7db197e80e5518d2591f468f. "
                    + "The port uses the repository's actual lattice fields and native Ring.choose rather "
                    + "than importing the upstream VOA stack. Upstream uses Lean v4.30.0 and mathlib "
                    + "c5ea00351c28e24afc9f0f84379aa41082b1188f; this native port uses Lean v4.35.0 and mathlib "
                    + "56a005855ea17e0b0958f73ec801ae140b0a1679. It is literature-attested, with no claim "
                    + "of independent mathematical novelty. The classical attribution is Zhu and Frenkel--Zhu.")),
                Paragraph(Text("Four-slot escape registration for associator_mem_zhuO is unfinished under "
                    + "https://github.com/the-omega-institute/trureturing/issues/28745. Missing evidence is a faithful "
                    + "typed reconstruction and equivalence for the entire original telescope D, positive-definiteness hD "
                    + "and arbitrary u,v,w, a lawful enrolled-template readout and actual-positive law, whole-family "
                    + "intervention and sensitivity, and actual observational dependence. Rank-zero and other constant "
                    + "degenerate fibres remain in scope; membership alone does not supply nonconstant sensitivity. "
                    + "No declared_validated registration is asserted.")),
                Paragraph(Text("This theorem establishes associator membership in O. It does not construct "
                    + "a quotient Ring or Algebra, prove the opposite stability statement, or assert an "
                    + "analytic CFT, string-theory model, or AdS/CFT correspondence."))),
            DescribeRole.Theorem))));
}
