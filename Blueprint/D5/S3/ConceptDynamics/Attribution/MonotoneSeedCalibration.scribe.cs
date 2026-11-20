using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class MonotoneSeedCalibrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict increases in the mass of nested events require distinct positive-mass seeds.",
        H("Positive-mass witnesses for nested events"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-seed-embedding"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/MonotoneSeedCalibration.positive_seed_embedding"),
            H("Distinct positive-mass seeds for successive increases"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let the finite events from index 0 through m be nested and have strictly increasing "
                        + "total real weight. There is an embedding from Fin m into the positive-weight "
                        + "seeds. The image of each index belongs to the next event and not to its current event.")),
                Paragraph(Text(
                    "The weight of each difference equals the increase in event weight. A positive sum "
                        + "gives a positive term. The differences are disjoint because each earlier event "
                        + "is contained in the event subtracted from every later increment.")),
                Paragraph(Text(
                    "For exact masses k/m on the binary grid, at least m positive-weight seeds are needed. "
                        + "Uniform seeds numbered from 0 to m minus 1 attain the bound by choosing label 1 "
                        + "when the seed index is below k. Reflecting the seed and reversing the probability "
                        + "index complements this event and preserves the uniform law."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula index = F.Id("k");
        Formula count = F.Id("m");
        Formula weight = F.Id("w");
        Formula events = F.Id("E");
        Formula seed = Call("i", index);
        Formula next = Call("E", Seq(index, Sp, Plus, Sp, D(1)));
        Formula current = Call("E", index);
        Formula positiveSupport = Seq(OpenBrace, F.Id("s"), Sp, Mid, Sp,
            D(0), Sp, Lt, Sp, Call("w", F.Id("s")), CloseBrace);
        return Disp(Seq(
            Forall, Sp, count, Sp, events, Sp, weight, Comma, Sp,
            Call("MonotoneOn", events, Call("Iic", count)), Sp, Land, Sp,
            Call("StrictMonoOn", Call("Mass", events, weight), Call("Iic", count)), Sp,
            Rightarrow, Sp, Exists, Sp, F.Id("i"), Colon, Sp,
            Call("Embedding", Call("Fin", count), positiveSupport), Comma, Sp,
            Forall, Sp, index, Colon, Sp, Call("Fin", count), Comma, Sp,
            seed, Sp, InMacro, Sp, next, Sp, Land, Sp, Neg, Open, seed, Sp, InMacro, Sp, current, Close));
    }
}
