using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeHistoryCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The interval normal form is complete for contextual executability, not just an endpoint cache.",
        H("Prime History Composition and Contextual Equivalence"),
        Blocks(
            Paragraph(Text(
                "Composition is chronological: the first form runs first. For source "
                + "intervals [l,u] and [l2,u2] and shifts d,d2, the composed source is "
                + "[max(l,l2-d),min(u,u2-d)] and the shift is d+d2. Empty intersections "
                + "produce the unique empty map. The interval is the constraint that "
                + "one actual intermediate state must satisfy both histories.")),
            Describe.Lean(
                DescribeId.Create("prime-history-concatenation-law"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryComposition.normal_append"),
                H("Actual concatenation descends to the computed composition"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("normal"), Open, F.Id("a"), Comma,
                    F.Id("v ++ w"), Close, Sp, Eq, Sp,
                    F.Id("compose"), Open, F.Id("normal(v)"), Comma,
                    F.Id("normal(w)"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof first derives the exact intermediate-state evaluation law "
                    + "for the closed formula, then uses translated prefix extrema and "
                    + "extensional uniqueness. Nonempty intervals are distinguished by "
                    + "their endpoints and one output value. Merely adding net shifts "
                    + "would lose the necessary intersection condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-partial-inverse"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryComposition.inverse_graph"),
                H("Reversal is a partial inverse with an explicit domain"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("graph"), Open, F.Id("inverse(s)"), Close, Sp, Eq, Sp,
                    F.Id("reverseGraph"), Open, F.Id("s"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse of [l,u] translated by d has interval [l+d,u+d] and "
                    + "translation -d. Its graph is proved to be the reversed graph, "
                    + "including singleton and empty cases. It is not asserted to be a "
                    + "total inverse on all capacity states. Existence of an actual word "
                    + "realizing this form follows from the normal-form realization owner."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-contextual-completeness"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryComposition.normal_eq_iff_contextual_accepts"),
                H("Boolean contextual tests detect every difference of normal forms"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("normal(v)"), Sp, Eq, Sp, F.Id("normal(w)")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed equality holds exactly when every capacity-bounded "
                    + "starting state and every prefix/suffix context give the same whole-word "
                    + "success/failure output. A domain difference is already an acceptance "
                    + "difference. If both words succeed with different endpoints, the "
                    + "previous exact horizon theorem supplies a suffix that separates them. "
                    + "This uses actual common intermediate states and the existing partial "
                    + "runner append law. The result quantifies over starting states; "
                    + "it does not posit a safe identification experiment on one unknown copy."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Contextual equality concerns total executability and final state. It is "
                + "not equality of intermediate transcripts, elapsed duration, probabilities "
                + "or costs. Group cancellation is unsafe at the guards: divide then "
                + "multiply is an identity only on its proper source interval. No group "
                + "action or Monster representation is inferred from the prime labels."))),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/PrimeHistoryNormalForm")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/BoundedPrimeHorizon"))
        ]));
}
