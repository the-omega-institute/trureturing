using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISLnDisplacedClassWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Displaced Class Words.",
        H("Type-A SLn Displaced Class Words"),
        Blocks(
            Paragraph(Text("Actual matrix displacement toward the small-field Section5 width kernel. A displaced coordinate block and its image commute by literal matrix support. This turns each of the THREE proved block commutators into FOUR genuine conjugates of the fixed permutation matrix. The geometric displacement condition is not a coverage assumption.")),
            Describe.Lean(
                DescribeId.Create("typea-partiislndisplacedclasswords-supported"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnDisplacedClassWords.Supported"),
                H("Supported"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal identity outside a principal coordinate block."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislndisplacedclasswords-padalong"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnDisplacedClassWords.padAlong"),
                H("padAlong"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual determinant-one reversing conjugator, over every field. The arbitrary permutation conjugator is normalized at the fixed coordinate; no SL conjugacy/class-width premise is supplied. -/ private theorem permutation_inverse_conjugate (sigma : Perm (Fin N)) (hs : Perm.sign sigma=1) (i : Fin N) (hi : sigma i=i) : ∃ c : SpecialLinearGroup (Fin N) F, c⁻¹*(permSL (F:=F) sigma hs)*c= (permSL (F:=F) sigma hs)⁻¹ := by classical obtain ⟨tau,htau⟩ := isConj_iff.mp (Perm.isConj_of_cycleType_eq (Perm.cycleType_inv sigma).symm) let t : Fˣ := (Units.map (Int.castRingHom F).toMonoidHom) (Perm.sign tau) let P : Matrix (Fin N) (Fin N) F := permMatrix (F:=F) tau let Q : Matrix (Fin N) (Fin N) F := permMatrix (F:=F) tau⁻¹ let D := scalarAt i t⁻¹ let E := scalarAt i t have hPQ : P*Q=1 := by dsimp only [P,Q] rw [(cycleClass% pMatrix_mul),inv_mul_cancel,(cycleClass% pMatrix_one)] have hQP : Q*P=1 := by dsimp only [P,Q] rw [(cycleClass% pMatrix_mul),mul_inv_cancel,(cycleClass% pMatrix_one)] have hDE : D*E=1 := scalarAt_inverse i t⁻¹ have hED : E*D=1 := scalarAt_inverse i t have hdet : det (D*P)=1 := by rw [det_mul,scalarAt_det,(cycleClass% pMatrix_det)] change ((t⁻¹:Fˣ):F)*(t:F)=1 simp let c : SpecialLinearGroup (Fin N) F := ⟨D*P,hdet⟩ have hinv : c⁻¹.val=Q*E := by have hh : c.val*(Q*E)=1 := by change (D*P)*(Q*E)=1 rw [mul_assoc,← mul_assoc P Q E,hPQ,one_mul,hDE] have hcc : c⁻¹.val*c.val=1 := congrArg Subtype.val (inv_mul_cancel c) calc c⁻¹.val = c⁻¹.val*(c.val*(Q*E)) := by rw [hh,mul_one] _ = Q*E := by rw [← mul_assoc,hcc,one_mul] refine ⟨c,?_⟩ apply Subtype.ext rw [SpecialLinearGroup.coe_mul,SpecialLinearGroup.coe_mul,hinv,(cycleClass% slPerm_inv)] change (Q*E)*(permMatrix (F:=F) sigma)*(D*P)=permMatrix (F:=F) sigma⁻¹ have hEC := scalarAt_commute sigma i hi t calc _ = Q*(permMatrix (F:=F) sigma)*P := by have hEC' : E*permMatrix (F:=F) sigma=permMatrix sigma*E := hEC calc _ = Q*(E*permMatrix sigma*D)*P := by simp only [mul_assoc] _ = _ := by rw [hEC',mul_assoc (permMatrix sigma) E D,hED,mul_one] _ = _ := by dsimp only [Q,P] rw [(cycleClass% pMatrix_mul),(cycleClass% pMatrix_mul)] rw [← mul_assoc,htau] private theorem displaced_four {S : Type u} [Group S] (h a b c : S) (hc : c⁻¹*h*c=h⁻¹) (hab : Commute (h*a*h⁻¹) b) : (List.ofFn (fun i : Fin 4 => ((![a,c,b,c*a*b] i)⁻¹*h*(![a,c,b,c*a*b] i)))).prod=a⁻¹*b⁻¹*a*b := by have hcomm : (h*a*h⁻¹)*b⁻¹*(h*a*h⁻¹)⁻¹=b⁻¹ := by rw [hab.inv_right.eq,mul_inv_cancel_right] calc _ = a⁻¹*((h*a*h⁻¹)*b⁻¹*(h*a*h⁻¹)⁻¹)*a*b := by simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil, Matrix.cons_val_zero,Matrix.cons_val_succ,mul_one] have h1 := hc have h2 : (c*a*b)⁻¹*h*(c*a*b)=b⁻¹*a⁻¹*h⁻¹*a*b := by calc _ = b⁻¹*a⁻¹*(c⁻¹*h*c)*a*b := by group _ = _ := by rw [hc] rw [hc,h2] group _ = _ := by rw [hcomm] private noncomputable def padEquiv (e : (Fin d ⊕ Fin d) ↪ Fin N) : ((Fin d ⊕ Fin d) ⊕ ((Set.range e)ᶜ : Set (Fin N))) ≃ Fin N := by classical exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e)) /-- Actual principal-block embedding for the selected coordinate injection."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiislndisplacedclasswords-actual-displaced-upper-twelve-class-factors"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnDisplacedClassWords.actual_displaced_upper_twelve_class_factors"),
                H("actual displaced upper twelve class factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twelve ACTUAL conjugacy-class factors reconstruct every upper target on a displaced block. Displacement is a literal permutation incidence, and all three commutators and the reversing conjugator are constructed. This is a local matrix-width conclusion, not full-group coverage."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
