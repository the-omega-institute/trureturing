using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class StrongSubadditivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/zhang2017subentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Bell pair and an independent maximally mixed qubit violate strong subadditivity of subentropy by exactly one twelfth.",
        H("A strong-subadditivity counterexample for subentropy"),
        Blocks(
            Paragraph(Text("Zhang, Singh and Pati ask the following question at arXiv:1510.08859v2, §7.1.")),
            Paragraph(Text("A similarly question can be asked for the strong subadditivity of subentropy: Q(ρ ABC) + Q(ρ B) ⩽ Q(ρ AB) + Q(ρ BC).")),
            Paragraph(Text("The formal conjecture quantifies over all three finite subsystem types and every positive trace-one joint density. Its AB marginal traces out C; its B marginal then traces out A. Its BC marginal uses only the associativity bijection of product labels before tracing out A.")),
            Describe.Lean(
                DescribeId.Create("subentropy-reassoc-state"),
                DeclarationHandle.Create(Module + ".reassocState"),
                H("Reassociating subsystem labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The canonical product associativity equivalence sends ((a,b),c) to (a,(b,c)). The existing InputInformationBalance.relabel applied to the inverse equivalence changes only these labels, allowing the existing bipartite partial trace to produce the BC marginal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subentropy-uniform-two-state"),
                DeclarationHandle.Create(Module + ".uniformTwo"),
                H("The maximally mixed qubit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matrix is diagonal on Fin 2 with both diagonal entries equal to one half. It is packaged directly in the canonical density-state carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subentropy-bell-state"),
                DeclarationHandle.Create(Module + ".bellState"),
                H("The canonical Bell density as a density state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state wraps the existing CHSHWitness.bellDensity, the outer product of its normalized Bell vector with its conjugate. Positivity and trace one are reused from bell_density_is_state; the existing Bell pure-state theorem supplies normalization and the maximally mixed marginal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subentropy-ssa-witness"),
                DeclarationHandle.Create(Module + ".witness"),
                H("The three-qubit witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The joint state is productState bellState uniformTwo. Thus A and B form a Bell pair, while C is an independent maximally mixed qubit. The construction uses the existing Kronecker-product density-state operation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subentropy-like-family"),
                DeclarationHandle.Create(Module + ".SubentropyLike"),
                H("The paper's spectral functional family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A family assigns a real value to each finite density state. It is continuous on density states, invariant under unitary conjugation, and agrees with the negative spectral residue sum on diagonal states with positive pairwise distinct entries. All coordinate types lie in Type, and all hypotheses retain their full finite-dimensional quantifiers.")),
                    Paragraph(Text("The consumed private identification theorem diagonalizes each density matrix and perturbs its ordered eigenvalues p by (1−ε)p+εq. The vector q has strictly positive decreasing entries proportional to N−i in the eigenvalue ordering; hence each positive perturbation has distinct positive entries and sum one. Taking ε=1/(k+1) gives convergence in the fixed eigenbasis. The spectral-formula theorem identifies both functionals on every approximant, and continuity of both, including continuousOn_matrixSubentropy, identifies their limits. Thus every such family equals subentropy, also at repeated or zero eigenvalues.")),
                    Paragraph(Text("canonicalSubentropy constructs an inhabitant from the determinant integral: its continuity uses DensityKernel, its unitary invariance uses isometric embedding, and its diagonal values use SpectralFormula. The result consumes this inhabitant and the identification theorem, so the quantified hypothesis set is nonempty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subentropy-ssa-conjecture"),
                DeclarationHandle.Create(Module + ".conjecture"),
                H("The strong-subadditivity question"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every SubentropyLike family Q and every finite tripartite density rho, assert Q(rho)+Q(rho_B)≤Q(rho_AB)+Q(rho_BC). Every marginal is constructed from that same joint density with the repository's partial-trace API. The BC reassociation is a pure relabelling, with no replacement state or additional assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subentropy-ssa-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Strong subadditivity fails with gap one twelfth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For the witness, rho_AB is the pure Bell state, rho_B is I₂/2, and rho_BC is I₄/4. The joint state is an isometric embedding of I₂/2. Its embedding matrix has entries J((a,b),c;d)=bellVector(a,b) when c=d and zero otherwise; Bell-vector normalization gives J-adjoint J=I₂.")),
                    Paragraph(Text("The determinant identity for rectangular Gram matrices preserves the defining subentropy integral under this embedding. Hence Q(rho)=Q(rho_B)=log 2−1/2, while Q(rho_AB)=0 and Q(rho_BC)=log 4−13/12.")),
                    Paragraph(Text("Using log 4=2 log 2 gives Q(rho)+Q(rho_B)−Q(rho_AB)−Q(rho_BC)=1/12. This positive gap contradicts the conjectured inequality. The proof uses one joint positive trace-one density and its actual marginals throughout."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-singh-pati-2017-subentropy-strong-subadditivity"),
                    ResolutionKind.Refuted)))));
}
