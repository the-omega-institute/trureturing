using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointSimultaneousLiteralHitsDocument : IScribeDocumentDefinition
{
    private static Formula S => F.Id("S");
    private static Formula N => F.Id("n");
    private static Formula E => F.Id("e");
    private static Formula Pi => F.Id("p");
    private static Formula Probability => Call("P", S, N);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every fixed finite collection of original-coordinate diagonals is hit with asymptotic probability one.",
        H("Simultaneous diagonal hits in finite separable permutations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simultaneous-literal-hit-probability"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits.simultaneousLiteralHitProbability"),
                H("Actual probability of hitting every specified diagonal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Probability, Eq, Call("actualMass", N, Seq(Pi, Mapsto, Sp, Forall, Sp,
                        E, InMacro, Sp, S, Comma, Sp, Call("hitsDiagonal", Pi, E)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same uniform length-n avoiding permutation is tested against every e in S. The event tests position minus value in the original coordinates. For the empty set the test is vacuous."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("simultaneous-literal-hits-limit"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits.simultaneous_literal_hits_limit"),
                H("Probability-one limit for every fixed finite offset set"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, S, Comma, Sp, Lim, Underscore, Grp(N, To, Infty), Probability, Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The set S is a fixed finite subset of the integers, chosen independently of n. Taking S to be a singleton recovers the limit for one fixed diagonal, and the singleton zero gives the existence of a fixed point with probability tending to one.")),
                    Paragraph(Text("Almost-sure recurrence in the actual marked stream supplies an eventual hit at each fixed offset. The fixed-prefix transfer gives a finite-permutation probability-one limit separately for each offset. Failure to hit all specified diagonals is a finite union of failures; its probability is bounded by the finite sum of the individual failure probabilities, which tends to zero. No independence of diagonal events is assumed.")),
                    Paragraph(Text("The result gives neither a rate nor a limit for sets varying with n. It does not claim multiple points on any single diagonal."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
