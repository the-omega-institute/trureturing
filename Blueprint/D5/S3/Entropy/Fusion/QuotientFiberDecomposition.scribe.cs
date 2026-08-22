using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Fusion;

internal sealed class QuotientFiberDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite source law splits into quotient entropy and weighted normalized-fiber entropy.",
        H("Quotient-Fiber Entropy Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-source-entropy-splits-over-quotient-fibers"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Fusion/QuotientFiberDecomposition."
                        + "quotient_fiber_entropy_decomposition"),
                H("Finite source entropy splits over quotient fibers"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and B be finite, let p be a nonnegative normalized mass on X, "
                            + "and let q map X to B. The quotient law is the deterministic "
                            + "pushforward of p along q.")),
                    Paragraph(Text(
                        "The graph map sends x to (q(x),x). Conditioning its pushforward at b "
                            + "constructs the normalized source law on the fiber over b, with "
                            + "zero contribution when the quotient mass at b vanishes.")),
                    Paragraph(Text(
                        "The first equality exposes the quotient-mass-weighted fiber sum. The "
                            + "second exposes the same decomposition through the canonical "
                            + "conditional-entropy aggregate. Injectivity of the graph map "
                            + "identifies graph-law entropy with source entropy, after which the "
                            + "finite Shannon chain rule supplies both conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Entropy(Formula law) => Call("H", law);

    private static Formula Push(Formula map, Formula law) => Call("push", map, law);

    private static Formula DecompositionFormula()
    {
        Formula sourceType = F.Id("X"), quotientType = F.Id("B");
        Formula mass = F.Id("p"), quotient = F.Id("q");
        Formula x = F.Id("x"), b = F.Id("b");
        Formula quotientLaw = Push(quotient, mass);
        Formula graphMap = Seq(
            x, Sp, Mapsto, Sp, Call("pair", Apply(quotient, x), x));
        Formula graphLaw = Push(graphMap, mass);
        Formula fiberLaw = Call("conditional", graphLaw, b);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, sourceType, Comma, Sp, quotientType, Comma, Sp,
            Call("Finite", sourceType), Sp, Land, Sp, Call("Finite", quotientType), Comma,
            RowBreak,
            mass, Colon, Sp, sourceType, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            quotient, Colon, Sp, sourceType, Sp, To, Sp, quotientType, Comma, RowBreak,
            Call("nonnegative", mass), Sp, Land, Sp,
            Sum, Underscore, Grp(x), Apply(mass, x), Sp, Eq, Sp, D(1), Sp,
            Rightarrow, RowBreak,
            Entropy(mass), Sp, Eq, Sp, Entropy(quotientLaw), Sp, Plus, Sp,
            Sum, Underscore, Grp(Seq(b, InMacro, Sp, quotientType)),
            Apply(quotientLaw, b), Entropy(fiberLaw), Sp, Land, RowBreak,
            Entropy(mass), Sp, Eq, Sp, Entropy(quotientLaw), Sp, Plus, Sp,
            Call("Hcond", graphLaw), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
