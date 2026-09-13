using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class BoundedPrimeWalkDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded exponent coordinates preserve every actual integer guard in a multiply/divide word.",
        H("Bounded Prime Walks"),
        Blocks(
            Paragraph(Text(
                "Fix a prime p and a natural capacity a. The live states are p to the e, "
                + "with 0 <= e <= a. A true input multiplies by p. A false input divides "
                + "exactly by p, and fails unless p divides the current integer. Every "
                + "result must still divide p to the a. Rejection is permanent along the word.")),
            Describe.Lean(
                DescribeId.Create("bounded-prime-integer-word-transport"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeWalk.run_transport"),
                H("The complete guarded integer execution is preserved"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("integerRun"), Open, F.Id("p^e"), Comma, F.Id("w"), Close,
                    Sp, Eq, Sp, F.Id("mapPow"), Open, F.Id("exponentRun"),
                    Open, F.Id("e"), Comma, F.Id("w"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Prime-power divisibility turns the upper arithmetic guard into e+1 <= a; "
                    + "exact division turns the lower guard into e>0. Induction on the actual "
                    + "input list transports every intermediate state and failure through "
                    + "the existing partial-DFA runner. Equal net displacement is not used "
                    + "as a substitute for the full guarded path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-prime-upward-probe"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeWalk.accepts_up"),
                H("A multiplication probe measures upper headroom"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("acceptUp"), Open, F.Id("e"), Comma, F.Id("k"), Close,
                    Sp, Eq, Sp, F.Id("decide"), Open,
                    F.Id("e"), Sp, Plus, Sp, F.Id("k"), Sp, Leq, Sp, F.Id("a"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof runs every repeated multiplication. It includes the empty "
                    + "probe and the first failed multiplication beyond capacity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-prime-downward-probe"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/BoundedPrimeWalk.accepts_down"),
                H("An exact-division probe measures the exponent"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("acceptDown"), Open, F.Id("e"), Comma, F.Id("k"), Close,
                    Sp, Eq, Sp, F.Id("decide"), Open,
                    F.Id("k"), Sp, Leq, Sp, F.Id("e"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The induction retains the guard at exponent zero; natural subtraction "
                    + "does not silently saturate an illegal division. These two probe "
                    + "families later supply the necessary distinguishing continuations."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Factorization/Automata/ReversiblePrimeThreshold"))]));
}
