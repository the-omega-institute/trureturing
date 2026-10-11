using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISLnBlockFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Block Factorization.",
        H("Type-A SLn Block Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiislnblockfactorization-actual-strict-block-factorization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBlockFactorization.actual_strict_block_factorization"),
                H("actual strict block factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual full off-block unitriangular reconstruction. Decreasing source blocks and increasing destination blocks preserve the noncommutative product. Every factor uses only its two true coordinate blocks. This is the next finite block-decomposition step for the class-width route."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnblockfactorization-actual-upper-block-factorization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBlockFactorization.actual_upper_block_factorization"),
                H("actual upper block factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The strict-block hypotheses above are DERIVED from each actual upper target, by removing its constructed diagonal-block matrix. -/ private theorem strict_after_diagonal (col : Fin N → Fin B) (hmono : Monotone col) (u : SpecialLinearGroup (Fin N) F) (hu : LayerDepth 1 (u.val-1)) : ∀ i j, ¬col i<col j → ((diagonalBlocks col u hu)⁻¹*u) i j=(1:Matrix (Fin N) (Fin N) F) i j := by classical let D := diagonalBlocks col u hu have hD : LayerDepth 1 (D.val-1) := by change LayerDepth 1 ((1+_)-1) rw [add_sub_cancel_left] intro i j hij;change (if col i=col j then (u.val-1) i j else 0)=0;split_ifs <;> simp [hu i j hij] have hV := (SLnNormalizer.Uplus N F).mul_mem ((SLnNormalizer.Uplus N F).inv_mem ((depth_memU D).mp hD)) ((depth_memU u).mp hu) intro i j hij by_cases h : col i=col j · have he : (D⁻¹*u) i j=(D⁻¹*D) i j := by simp only [SpecialLinearGroup.coe_mul,Matrix.mul_apply] apply Finset.sum_congr rfl intro t ht by_cases hti : col t=col i · rw [diagonalBlocks_entry,if_pos (hti.trans h)] · rw [diagonal_inverse_off col u hu i t (Ne.symm hti),zero_mul,zero_mul] rw [he,inv_mul_cancel] rfl · have hji : j.val < i.val := by by_contra hh have hle : i≤j := by change i.val≤j.val;omega have hcol := hmono hle exact hij (lt_of_le_of_ne hcol h) have hne : i≠j := fun he => h (congrArg col he) simp only [Matrix.one_apply,if_neg hne] exact ((SLnNormalizer.mem_Uplus_iff _).mp hV).1 i j hji /-- all coordinates of an arbitrary upper target: B diagonal-block factors and B squared actual rectangular factors. The order is exact. Each factor is supported on one or two genuine blocks, ready for actual class transport. No diagonal/strict-block/reconstruction premise remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnblockfactorization-actual-upper-eighty-chunk-factorization"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBlockFactorization.actual_upper_eighty_chunk_factorization"),
                H("actual upper eighty chunk factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A CONSTANT number of genuinely small supported factors for every actual upper target. The 80 consecutive chunks and both support-cardinality bounds are constructed from N<=80s. Identity slots pad the exact length 80+80²=6480; no factor count depends on rank or target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnblockfactorization-actual-long-cycle-chunk-bounds"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBlockFactorization.actual_long_cycle_chunk_bounds"),
                H("actual long cycle chunk bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The printed large-rank shape SUPPLIES the 80-chunk hypothesis and the local displacement size d=2*(L/8), with no extra rank-width premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
