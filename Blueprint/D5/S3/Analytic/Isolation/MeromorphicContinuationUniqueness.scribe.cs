using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class MeromorphicContinuationUniquenessDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef IdentityTheorem =
        LibraryNoteRef.Create("D5/L/Zeros/jaiswar2021identity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal-form meromorphic continuations are fixed by their values on a nonempty open set.",
        H("Uniqueness of Meromorphic Continuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("meromorphic-continuations-agreeing-on-an-open-set-are-unique"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness."
                    + "meromorphic_continuation_unique"),
                H("Meromorphic continuations agreeing on an open set are unique"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("Omega"), Comma, Sp, F.Id("D"),
                    Subseteq, Sp, Mathbb, Grp(F.Id("C")), Comma, RowBreak,
                    Forall, Sp, F.Id("f"), Comma, Sp, F.Id("g"), Colon,
                    Mathbb, Grp(F.Id("C")), To, Mathbb, Grp(F.Id("C")), Comma, RowBreak,
                    Operatorname, Grp(F.Id("IsOpen")), Open, F.Id("Omega"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("IsPreconnected")), Open, F.Id("Omega"), Close,
                    Sp, Land, Sp, RowBreak,
                    Operatorname, Grp(F.Id("IsOpen")), Open, F.Id("D"), Close,
                    Sp, Land, Sp, F.Id("D"), Neq, Emptyset,
                    Sp, Land, Sp, F.Id("D"), Subseteq, Sp, F.Id("Omega"),
                    Sp, Land, Sp, RowBreak,
                    Operatorname, Grp(F.Id("MeromorphicNFOn")),
                    Open, F.Id("f"), Comma, F.Id("Omega"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("MeromorphicNFOn")),
                    Open, F.Id("g"), Comma, F.Id("Omega"), Close,
                    Sp, Land, Sp, RowBreak,
                    Operatorname, Grp(F.Id("EqOn")),
                    Open, F.Id("f"), Comma, F.Id("g"), Comma, F.Id("D"), Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("EqOn")),
                    Open, F.Id("f"), Comma, F.Id("g"), Comma, F.Id("Omega"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromLiterature(IdentityTheorem),
                Blocks(
                    Paragraph(Text(
                        "Let Omega be an open preconnected complex domain and let D be a "
                        + "nonempty open subset of Omega. If f and g are meromorphic in normal "
                        + "form on Omega and agree pointwise on D, then they agree pointwise "
                        + "throughout Omega. Every premise displayed here occurs in the Lean "
                        + "type; in particular, D cannot be empty and the conclusion includes "
                        + "the canonical values at poles.")),
                    Paragraph(Text(
                        "Normal form is the faithful Mathlib representation needed for the "
                        + "source's sphere-valued meromorphic functions. Bare `MeromorphicOn` "
                        + "allows a function to be changed arbitrarily at discrete pole points, "
                        + "so pointwise uniqueness would be false for that predicate. "
                        + "`MeromorphicNFOn` fixes every pole to one canonical default value; it "
                        + "does not assert that the functions are analytic or pole-free.")),
                    Paragraph(Text(
                        "The proof delegates the analytic content to Mathlib's local identity "
                        + "principles `MeromorphicAt.frequently_eq_iff_eventuallyEq` and "
                        + "`MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`. The "
                        + "repository wrapper only proves that local agreement and local "
                        + "disagreement form an open separation, then invokes preconnectedness. "
                        + "No Laurent-series identity argument is reproved.")),
                    Paragraph(Text(
                        "Repository search found the related theorem "
                        + "`D5/S3/Zeros/CompletedZeta.analytic_continuation_unique`, but that "
                        + "declaration assumes both continuations are analytic and therefore does "
                        + "not cover this meromorphic atom. This theorem proves uniqueness only: "
                        + "it constructs no continuation and assumes no Euler-product, functional "
                        + "equation, or absence of poles."))),
                DescribeRole.Theorem))));
}
