using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostBrstGhostNumberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostBrstGhostNumber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unmodified original BRST charge raises integral ghost number on every algebraic tensor state.",
        H("Ghost Number Of The Original Tensor BRST Charge"),
        Blocks(Describe.Lean(
            DescribeId.Create("latticebcghostbrst-ghost-degree"),
            DeclarationHandle.Create(Prefix + "J_Q_commutator"),
            H("The actual charge has degree one on the entire original State"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let D be any original LatticeData: a finite rank, an integral symmetric "
                    + "matrix and even diagonal entries, with no positivity or nondegeneracy hypothesis. "
                    + "Let H be any complex matrix on Fin(D.rank), including the zero matrix. "
                    + "On exactly State(D)=Carrier(D) tensor over Complex with Fock(Complex), define "
                    + "J(D) by the identity on matter tensored with the actual signed-occupation ghost "
                    + "number operator. The statement is J(D) times Q(D,H) minus Q(D,H) times J(D) "
                    + "equals Q(D,H), as an endomorphism equality on the entire algebraic tensor space. "
                    + "It covers arbitrary finite sums of pure tensors and arbitrary ghost superpositions.")),
                Paragraph(Text("There is no fixed rank, inverse-Gram identity, Virasoro hypothesis, "
                    + "nilpotence hypothesis, assumed homogeneity or assumed commutator premise. "
                    + "The charge Q is not replaced. It is the original finsum of A(D,H,n), where "
                    + "A=C(-n) composed with M(n)+(1/2) times N(n). The original N is C(-n) "
                    + "composed with G(n) when -1<=n and G(n) composed with C(-n) otherwise. "
                    + "There is no added outer-ordering sign, intercept, cutoff or conjugation.")),
                Paragraph(Text("The actual c-mode degree law lifts through the existing tensor-map "
                    + "algebra homomorphism, and the actual ghost stress is neutral. Matter endomorphisms "
                    + "commute with J because they act on the other tensor factor. The commutator "
                    + "product rule therefore gives degree one to each original A summand, in both "
                    + "outer-order branches. Generic tensor lifts and scalar algebra are consumed helpers. "
                    + "For each original tensor state psi, A_finite(D,H,psi) and A_finite(D,H,J(psi)) "
                    + "are reused. A finite-support-preserving image transports J through the first "
                    + "finsum, and finite-sum subtraction combines the two original charges. The actual "
                    + "summand commutator then gives Q(psi), without inventing a uniform global cutoff.")),
                Paragraph(Text("This is grading infrastructure for the same original research goal. "
                    + "The separate supplied critical nilpotence theorem assumes rank 26 and both "
                    + "Gram inverse identities; none of those assumptions is imported into this claim. "
                    + "Neither result is a cohomology computation or a complete string theory. "
                    + "No no-ghost theorem, physical spectrum, amplitudes or AdS/CFT correspondence "
                    + "is asserted here."))),
            DescribeRole.Theorem))));
}
