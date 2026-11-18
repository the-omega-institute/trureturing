using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OriginalWReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor reflection for actual dual symmetric powers of a faithful two-dimensional elementary-abelian representation.",
        H("Tensor reflection for the original two-dimensional module"),
        Blocks(
            Paragraph(Text("Let K be any field of prime characteristic p, E a finite nontrivial abelian group written additively with p e=0 for every e, and rho a faithful representation on a two-dimensional K-vector space W. The carriers K and W have type Type in this Mathlib symmetric-power API; E has an independent universe. For every positive i define V_i as the ordinary linear dual of the actual Mathlib quotient SymmetricPower K (Fin (i-1)) W, with the induced contragredient action. In particular V_1 is the dual of Sym^0 W. No polynomial model is substituted into this definition.")),
            Paragraph(Text("Put q=card E and M=the literal direct sum of V_p,V_(2p),...,V_q. A module P is M-relatively projective when it is an equivariant retract of X tensor M for some arbitrary representation X. The relation A~_M B is the original RelativeStableIso: two intertwining maps compose to the identities modulo the original RelativeFactors ideal. Neither P nor X is required to be finite-dimensional.")),
            Describe.Lean(
                DescribeId.Create("original-w-tensor-reflection"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/OriginalWReflection.originalW_tensor_reflection"),
                H("Reflect both low digits in the original relative category"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For natural a,b,u,v with u,v<p and positive i=pa+u<q and j=pb+v<q, the theorem proves V_(pa+p-u) tensor V_(pb+p-v) ~_M V_i tensor V_j. The reflected indices are positive by u,v<p. There is no bound on i+j or u+v and no condition on a binomial coefficient or carries. The field K need not be finite. Zero residues and characteristic two are retained; when a reflected index reaches q the actual V_q summand is used.")),
                    Paragraph(Text("The proved two-dimensional normal form constructs a basis and an injective additive parameter alpha:E->K from faithfulness and the exponent-p action. The genuine symmetric-power quotient equivalence then supplies all positive-index contragredient model equivalences at once, including degrees at least p, without factorial division. Their literal direct sum identifies M and their actual tensor product identifies each endpoint. The arbitrary-embedding reflection is applied along this constructed alpha. Transporting its relative stable maps back conjugates both inverse errors and keeps the original unrestricted P and X witnesses. No basis, embedding, polynomial-model equivalence or transport assertion is assumed by the final theorem.")),
                    Paragraph(Text("The substantive reflection mechanism is the previously proved single-factor recurrence along alpha: V_(p-1) tensor V_(pa+u) ~_M V_(pa+p-u) for 1<=u<p. Its induction uses cancellation of a specific polynomial summand with a proved invertible top-line scalar. The square identity for V_(p-1) is derived after that induction. Applying the same reflection factor to both tensor factors and then its square gives the positive-residue case; original relative-projective retracts handle zero residues. The coordinate transportation here is the application of that mechanism to the paper's actual W."))),
                DescribeRole.Theorem),
            Paragraph(Text("The external anchor is Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, Conjecture 3.7(b). The recurrence follows their Proof of Corollary 1.3. This theorem supplies the original faithful two-dimensional formulation of part (b), with the displayed individual index bounds and without sum or carry restrictions. It does not prove the false unconditional part (a); the corrected classification of part (a) is separate. No novelty, uniqueness or literature-priority claim is made.")),
            Paragraph(Text("The auxiliary typed DependentFamily registration audit remains unfinished in https://github.com/the-omega-institute/trureturing/issues/30512. No declared_validated status is asserted.")))));
}
