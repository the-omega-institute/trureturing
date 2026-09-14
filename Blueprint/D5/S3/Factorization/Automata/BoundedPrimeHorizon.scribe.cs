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
                "The bounded runner records whether the entire requested word was legal. "
                + "At horizon H, compare "
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
                DescribeRole.Theorem))));
}
