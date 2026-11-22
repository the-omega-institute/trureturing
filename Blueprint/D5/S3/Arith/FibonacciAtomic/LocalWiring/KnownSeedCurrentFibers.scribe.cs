using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class KnownSeedCurrentFibersDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers.";

    private static Formula N => F.Id("n");
    private static Formula X => F.Id("X");
    private static Formula P => F.Id("p");
    private static Formula C => F.Id("c");
    private static Formula Fib(Formula index) => Seq(F.Id("F"), Underscore, Grp(index));
    private static Formula Count(string name) => Seq(F.Id("N"), Underscore, Grp(F.Id(name)));
    private static Formula TwoPower(Formula exponent) => Seq(D(2), Caret, Grp(exponent));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Starting from the known alpha leaf, the current physical shape leaves precisely one free "
        + "label bit at each cherry. The exact finite counts and the entire next presence map follow.",
        H("Known-alpha current fibres and complete one-step predictions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gpo-known-seed-next-presence-map"),
                DeclarationHandle.Create(Prefix + "nextPresence"),
                H("Read a complete next-step presence map"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Next", X, P), Eq, D(1), Sp, Iff, Sp, Call("Present", X, P), Eq, D(1),
                    Sp, Lor, Sp, Open, P, Neq, Sp, Varepsilon, Sp, Land, Sp,
                    Call("BetaLeaf", X, Call("Parent", P)), Eq, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here epsilon is the empty physical word and Parent removes the final bit. "
                        + "The output is a Boolean for every finite word, not only the words present now. "
                        + "Old words persist and exactly the two children of each current beta leaf are added. "
                        + "At the empty word the parent term is disabled.")),
                    Paragraph(Text(
                        "Each real next update has this same physical presence map. The orientation chosen "
                        + "by a newly splitting beta changes only the order of its two new leaf labels."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gpo-known-alpha-fibres-exact-count-and-next-readout"),
                DeclarationHandle.Create(Prefix + "exact_known_seed_fibres"),
                H("The four Fibonacci counts and the complete current fibre"),
                StatementSource.FromAuthor(Disp(Seq(
                    C, Eq, Fib(Seq(N, Minus, D(1))), Quad, Sp,
                    Count("fiber"), Eq, TwoPower(C), Quad, Sp,
                    Count("shapes"), Eq, TwoPower(Seq(Fib(N), Minus, D(1))), Quad, Sp,
                    Count("labelled"), Eq, TwoPower(Seq(Fib(Seq(N, Plus, D(1))), Minus, D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At each attained horizon n≥2 and attained physical shape S, c is the number "
                        + "of physical cherry addresses. The labelled fibre is in bijection with all "
                        + "Boolean assignments on those addresses, where each bit says that the left "
                        + "leaf at its cherry is beta. The counts are of actual states of the known alpha "
                        + "seed under exactly n serial local steps.")),
                    Paragraph(Text(
                        "The shape fixes the heavier child at each rank at least three by the two "
                        + "different Fibonacci leaf counts. At rank two the two physical orientations "
                        + "have the same cherry shape, but different labelled trees. Every assignment "
                        + "is realized jointly in one whole tree.")),
                    Paragraph(Text(
                        "Write a for the physical left-child bit. At any current cherry address p, "
                        + "the next reply at p followed by aa is exactly that cherry's bit. Thus "
                        + "different labelled states in the same current shape fibre have different "
                        + "entire next maps, while the reconstructed labels determine all present "
                        + "and absent replies. No prediction of a future orientation is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
