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
                StatementSource.FromAuthor(NormalAppendFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof first derives the exact intermediate-state evaluation law "
                    + "for the closed formula, then uses translated prefix extrema and "
                    + "extensional uniqueness. Nonempty intervals are distinguished by "
                    + "their endpoints and one output value. Merely adding net shifts "
                    + "would lose the necessary intersection condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-contextual-run-completeness"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryComposition.normal_eq_iff_contextual_run"),
                H("Contextual runs characterize the normal form"),
                StatementSource.FromAuthor(ContextualRunFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality of normal forms is equivalent to equality of the exact partial "
                    + "runner in every prefix and suffix context and at every live state."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Contextual equality concerns total executability and final state. It is "
                + "not equality of intermediate transcripts, elapsed duration, probabilities "
                + "or costs. Group cancellation is unsafe at the guards: divide then "
                + "multiply is an identity only on its proper source interval. No group "
                + "action or Monster representation is inferred from the prime labels."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Factorization/Automata/PrimeHistoryNormalForm"))]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Words() => Call("List", F.Id("Bool"));

    private static Formula FinState() =>
        Call("Fin", new Formula.Binary(F.Id("a"), FormulaBinaryOperator.Add, D(1)));

    private static Formula Append(Formula left, Formula right) =>
        QualifiedCall("List", "append", left, right);

    private static Formula Normal(string word) => Call("normal", F.Id("a"), F.Id(word));

    private static Formula Context(string word) =>
        Append(Append(F.Id("before"), F.Id(word)), F.Id("after"));

    private static Formula NormalAppendFormula() => Disp(Universal("a", Naturals(),
        Universal("v", Words(), Universal("w", Words(),
            Equal(
                Call("normal", F.Id("a"), Append(F.Id("v"), F.Id("w"))),
                Call("compose", Normal("v"), Normal("w")))))));

    private static Formula ContextualRunFormula() => Disp(Universal("a", Naturals(),
        Universal("v", Words(), Universal("w", Words(),
            IffFormula(
                Equal(Normal("v"), Normal("w")),
                Universal("before", Words(), Universal("after", Words(),
                    Universal("e", FinState(),
                        Equal(
                            Call("run", F.Id("a"), F.Id("e"), Context("v")),
                            Call("run", F.Id("a"), F.Id("e"), Context("w")))))))))));
}
