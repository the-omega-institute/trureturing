using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class FractionalEvolutionPhaseObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary unitary queries preserve global-phase blindness, whereas prescribed fractional branches can separate their full output channels.",
        H("Ordinary queries and the prescribed fractional branch"),
        Blocks(
            Definition("query", "Ordinary signed oracle queries",
                "A true sign selects the adjoint of the oracle matrix; a false sign selects the oracle itself."),
            Definition("controlledQuery", "The controlled query for comparison",
                "On control zero this matrix applies the signed query; on control one it is identity. It is the source model's controlled query and does not occur in the ordinary circuit run."),
            Definition("Circuit", "Fixed finite circuits",
                "For dimension d, workspace dimension m+1, and natural query count N, a circuit contains N+1 unitary inter-query gates and N Boolean signs. These data are fixed before the oracle and its logarithm are quantified. N may be zero."),
            Definition("run", "The ordered ordinary-query product",
                "Start at W zero and fold the ordered list of N slots by left multiplication with W at the next index and identity tensor the signed oracle. The product is W N Q N through W one Q one W zero. The identity tensor factor acts on the entire workspace."),
            Definition("initialization", "The fixed basis-zero embedding",
                "The initialization matrix J maps input psi to workspace basis zero tensor psi. Its entry is one exactly when the workspace coordinate is zero and the target coordinate equals the input index; all other entries vanish."),
            Definition("Successful", "Uniform full-output success",
                "For every pair U,H with U=exp(iH), H Hermitian, and real spectrum contained in [delta,2 pi), compare the conjugation channels of run(A,U) J and J exp(itH). Their difference must have the original Harrow diamondNorm at most ENNReal.ofReal epsilon. This norm is the unhalved supremum of trace norms over all positive semidefinite trace-one inputs with an input-sized untouched reference. The entire workspace and target output is retained."),
            Definition("claim", "A universal ordinary-query upper bound",
                "There exists a real universal constant C>0. For every real t and delta strictly between zero and one, epsilon strictly between zero and one half, and positive natural dimension d, there exist natural m,N and a fixed Circuit d m N with N at most C times inverse delta times the natural logarithm of inverse epsilon, and Successful A t delta epsilon. The circuit existential precedes every U,H in Successful."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("The uniform upper bound fails"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use t=delta=1/2, epsilon=1/4, and d=2. The logarithms are diagonal with entries pi/2 and 3 pi/2 in opposite orders. Their oracle exponentials are U=diag(i,-i) and -U, and both logarithms satisfy the half-open spectral promise. Every ordinary query changes sign when U is replaced by -U, including adjoint queries. Induction over the actual ordered fold gives run(A,-U)=(-1)^N run(A,U), so the initialized implementation channels agree for every finite workspace and every natural N.")),
                    Paragraph(Text("The input is the equal-superposition density on the target tensored with reference basis zero. At t=1/2 the two ideal stabilized full outputs are orthogonal pure states with relative phases i and -i, initialized at workspace basis zero. Their unhalved trace-norm separation is two. Each successful implementation would lie within trace norm one quarter of its corresponding target on this admissible stabilized input. The triangle inequality would then bound two by one half, a contradiction. No query-count estimate is needed to reach this contradiction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("liu-wesolowski-2026-ordinary-fractional-evolution"),
                    ResolutionKind.Refuted)),
            Paragraph(Text("The source is Liu, Wesolowski, Thompson, Gu and Pira, Optimal query complexity for fractional quantum evolution, arXiv:2610.01940v1: Definitions 1-3, Appendix B, and the unnumbered uncontrolled-access question in Section V. The ordinary-query substitution leaves the controlled upper bound and the ordinary-query lower bound outside the assertion considered here. The global-phase obstruction is known prior work."))
        )));

    private static DocumentBlock Definition(string selector, string title, string body) =>
        Describe.Lean(DescribeId.Create(selector.ToLowerInvariant()), DeclarationHandle.Create(Module + "." + selector),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);
}
