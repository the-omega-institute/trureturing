using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class BoundedPrimeHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both guard distances, rather than current legality alone, determine the exact finite-horizon state.",
        H("Two-Boundary Observation of a Prime Register"),
        Blocks(
            Paragraph(Text(
                "Use the actual bounded runner from BoundedPrimeWalk. The output records "
                + "whether the entire requested word was legal. At horizon H, compare "
                + "all words of total length at most H, including the empty word.")),
            Describe.Lean(
                DescribeId.Create("bounded-prime-horizon-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeHorizon.finite_horizon_kernel"),
                H("The exact two-boundary profile"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("profile"), Open, F.Id("e"), Close,
                    Sp, Eq, Sp, Open, F.Id("min(e,H)"), Comma, F.Id("min(a-e,H)"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two live states have equal responses to every such word exactly when "
                    + "the displayed profiles agree. Necessity uses repeated multiplication "
                    + "and division. Sufficiency is induction over the word: first-step "
                    + "guards agree, and successful successors have equal profiles at H-1. "
                    + "Mixed paths, underflow and overflow are all covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-prime-realized-profile-count"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeHorizon.profile_classification"),
                H("Every profile is realized and counted"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("cardProfileWithReject"), Sp, Eq, Sp,
                    F.Id("min(a,2H)"), Sp, Plus, Sp, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A concrete code collapses only the central interval. It is surjective "
                    + "onto Fin(min(a,2H)+1), and its kernel is exactly the response kernel. "
                    + "The separate rejection point remains visible on the empty word. "
                    + "This is not a claim that a fixed-H quotient updates autonomously "
                    + "for arbitrarily many later steps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-prime-shortest-separator"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeHorizon.shortest_separation"),
                H("The shortest pairwise distinguishing continuation"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("shortestLength(e,f)"), Sp, Eq, Sp, F.Id("min(e+1,a-f+1)")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For e<f, a separator of length at most H exists exactly when the "
                    + "displayed minimum is at most H. A pure downward or upward word "
                    + "attains the bound. The profile theorem excludes every shorter mixed "
                    + "word. This is pairwise distinguishability, not one fixed probe that "
                    + "identifies every unknown state without disturbance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-prime-complete-separation-threshold"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeHorizon.full_separation_threshold"),
                H("The sharp worst-case horizon"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("completeSeparation"), Open, F.Id("H"), Close,
                    Sp, Eq, Sp, Open, F.Id("a"), Sp, Leq, Sp, F.Id("2H"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a>2H, the actual distinct central exponents H and H+1 still agree "
                    + "on all H-step probes. If a<=2H, equal lower and upper clipped "
                    + "distances force equal exponents. Thus the least horizon is ceiling(a/2)."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Factorization/Automata/BoundedPrimeWalk"))]));
}
