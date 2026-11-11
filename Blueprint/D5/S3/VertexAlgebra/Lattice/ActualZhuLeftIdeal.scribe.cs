using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuLeftIdealDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualZhuLeftIdeal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original full Zhu left ideal",
        H("Original full Zhu left ideal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualzhuleftideal-translation-star-circle"),
                DeclarationHandle.Create(Prefix + "translation_star_circle"),
                H("Translation residue equals the original circle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every original positive-definite lattice datum D, natural weight K, original state a in grade K and unrestricted state b, star(Ta + K a,b) is literally the existing complete circle(K,a,b). The proof shifts the derivative star row and the weight star row onto the same range, including the bottom and top endpoints. Pascal and upper absorption cancel each coefficient to choose(K,i). The original native translation, state derivative and generalized binomial coefficients supply the interfaces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhuleftideal-star-left-mem-zhuo"),
                DeclarationHandle.Create(Prefix + "star_left_mem_zhuO"),
                H("Left-argument stability on the literal span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For all original states o and v, if o belongs to ActualZhuFinite.zhuO(D), then star(o,v) belongs to the same submodule. On a literal circle generator the translation residue identity rewrites it as star(Ta + K a,b); the proved full actual associator and the circle for star(b,v) give membership. Linear span induction extends this to all o. Stability and associativity are conclusions from their proved native suppliers, never extra structure fields."))),
                DescribeRole.Theorem),
            Paragraph(Text("The source-faithful native port consumes cbz_coeff_identity and zhuMul_L_base from ZhuModule.lean and left_ideal_gen_of_assoc from ZhuRingResidue.lean, Fedor K. Popov, Lean_VOA commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, Apache-2.0, with classical Zhu and Frenkel-Zhu attribution. Native Lean 4.35 and its pinned Mathlib replace upstream Lean 4.30 and its distinct Mathlib pin, as recorded in the reference note. This is literature-attested implementation, not an independent novelty claim.")),
            Paragraph(Text("The dependent-family audit remains incomplete: exact source reconstruction, an enrolled readout, the actual-positive law, whole-family variation and sensitivity, actual observational dependence and current source binding are still required. See https://github.com/the-omega-institute/trureturing/issues/28745.")))));
}
