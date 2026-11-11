using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetSectionConjugacyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetSectionConjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted semilinear averaging for principal-unit section conjugacy.",
        H("The finite-sum obstruction solver"),
        Blocks(
            Paragraph(Text("A finite quotient section-comparison cocycle can be solved without dividing by the order of the acting group when the coefficient action admits a weighted trace-one element. The coefficient space is only required to be an additive K-module; this keeps the lemma applicable to the unrestricted End_F(K) top layer of the odd-prime jet radical.")),
            Describe.Lean(DescribeId.Create("odd-prime-jet-weighted-semilinear-cocycle"),
                DeclarationHandle.Create(Owner + "weighted_semilinear_cocycle_coboundary"),
                H("Weighted semilinear cocycles are coboundaries"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Γ be a finite group, σ assign field endomorphisms to its elements, and ρ act additively on a K-module W. Assume σ respects multiplication, ρ is σ-semilinear, and f satisfies the crossed-homomorphism identity f(gh)=f(g)+ρ_g(f(h)). If θ has weighted trace ∑_h σ_h(θ)=1, then the explicit finite sum b=∑_h σ_h(θ)·f(h) satisfies f(g)=b−ρ_g(b) for every g. The proof reindexes by left multiplication and uses no inverse of |Γ|, so it remains valid when the quotient order is divisible by the characteristic."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-weighted-associativity-defect"),
                DeclarationHandle.Create(Owner + "weighted_semilinear_associativity_defect"),
                H("Weighted averaging removes the graded associativity defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let c(g,h) be a W-valued defect satisfying c(g,h)+c(gh,k)=ρ_g(c(h,k))+c(g,hk). With the same semilinear action and weighted trace-one element, the explicit sum over k with weights σ_{ghk}(θ) turns this four-term identity into c(g,h)+a(gh)=ρ_g(a(h))+a(g), where a(g)=∑_k σ_{gk}(θ)·c(g,k). This is the obstruction equation needed to correct arbitrary quotient representatives one jet layer at a time; it avoids dividing by the group order."))),
                DescribeRole.Theorem)
        )));
}
