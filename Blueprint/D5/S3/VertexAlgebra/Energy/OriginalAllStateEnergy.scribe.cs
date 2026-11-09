using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Energy;

internal sealed class OriginalAllStateEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform order-two-weight analytic bounds on the literal original all-state lattice fields.",
        H("Original all-state energy bounds"),
        Blocks(
            Paragraph(Text("D is the original integral even LatticeData with positive definite gramReal(D). Carrier(D), Y(D,s), normD(v)=sqrt(Re Hm(v,v)) and sugawaraMode(D,H,0) are the original objects. Both complex inverse laws H*gramComplex(D)=1 and gramComplex(D)*H=1 are required. No desired-bound premise, assumed unitary VOA, alternate positive completion, determinant-unit condition, ghost intercept or input-support factor occurs.")),
            Describe.Lean(
                DescribeId.Create("original-all-state-homogeneous-energy-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Energy/OriginalAllStateEnergy.homogeneous_energy_bound"),
                H("Uniform homogeneous order 2W"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every W:N and s:Carrier(D) in the literal original grade W, there exists C:R with C>0, chosen before all m:Z and all v:Carrier(D), such that normD((Y(D,s)[[m+W-1]])v) <= C*(1+abs(m:R))^(2*W)*normD(((1+sugawaraMode(D,H,0))^(2*W))v). C depends on the fixed state, never on the input charge, oscillator degree or support size.")),
                    Paragraph(Text("The existing charged positive-mode proof bounds the raw nonnegative mode by chargedConstant(a)*(E+1)^(2*d). Its opposite-charge adjoint proof bounds negative raw modes by chargedConstant(-a)*(F+1)^(2*d) at the actual output grade. These proof terms are factored once into charged_pre_relaxation_grade_le and consumed both by the retained generator bound and by the new bounded-endpoint seed. The latter has order 2*d when E,F<=M, without applying the relaxed generator endpoint a second time. Charge zero uses the literal identity with seed (1,0).")),
                    Paragraph(Text("The single arbitrary-charge recurrence gives order 2*d+wordWeight+length. For every nonzero coefficient (a,e) of the fixed homogeneous state, mem_grade_iff gives d+oscillatorEnergy(e)=W, and occurrence_weight and length<=wordWeight imply order<=2*W. stateField_expansion reconstructs the actual field. Triangle inequality is used only over the fixed state coefficients, without asserting monomial orthogonality. The positive constant is 1+sum_(a,e) abs(coeff(s,a,e))*seedConstant(a)*wordConstant(occurrences(e)).")),
                    Paragraph(Text("At mode m+W-1 the output grade is E-m. Negative output vanishes; otherwise M=max(E,E-m) gives M+1<=(1+abs(m))*(E+1). The original energy_bound_of_grades performs exact finite square recombination using actual Sugawara grade orthogonality and the energy-power eigenformula. Distinct input grades have distinct shifted output grades. Zero state, W=0, zero charge and rank zero remain included without positive-rank or nonzero-state hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-all-state-finite-energy-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Energy/OriginalAllStateEnergy.finite_energy_bound"),
                H("Arbitrary finite-state common Laurent bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every original finite state s let Wmax be the finite supremum of E.toNat over stateEnergies(D,s), with empty supremum zero. Positivity makes this exactly max(stateEnergies(s) union {0}). There exists C>0 before all n:Z and all v:Carrier(D) such that normD((Y(D,s)[[n]])v) <= C*(1+abs(n:R))^(2*Wmax)*normD(((1+sugawaraMode(D,H,0))^(2*Wmax))v).")),
                    Paragraph(Text("Decompose only the fixed state s into its actual grade projections s_E. Its homogeneous component uses circle index n-E+1. The inequality 1+abs(n-E+1)<=(E+2)*(1+abs(n)) moves every component to a common Laurent scale. Power domination normD(T^k v)<=normD(T^N v) for k<=N is obtained from the existing orthogonal finite-grade square recombination and (E+1)^k<=(E+1)^N. Triangle inequality over the fixed state components gives C=1+sum_E stateConstant(s_E)*(E+2)^(2*E). Components of different fixed-state weights are not assumed orthogonal."))),
                DescribeRole.Theorem),
            Paragraph(Text("The original charged order 2d and neutral order 2w public endpoints retain their types and strength. Existing Bakalov-Kac, Matsuo-Nagatomo, Carnahan and Mathlib source attributions are retained; there is no literature-novelty claim. Hilbert completion, smearing, adjoint-closure equality, essential self-adjointness, strong locality, no-ghost, full string theory and AdS/CFT remain separate obligations."))),
        []));
}
