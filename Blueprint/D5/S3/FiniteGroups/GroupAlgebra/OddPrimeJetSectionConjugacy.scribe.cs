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
                DescribeRole.Theorem)
        )));
}
