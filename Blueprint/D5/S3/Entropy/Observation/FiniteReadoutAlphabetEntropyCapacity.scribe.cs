using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class FiniteReadoutAlphabetEntropyCapacityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Observation/FiniteReadoutAlphabetEntropyCapacity."
            + "finite_readout_alphabet_entropy_capacity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite realized readout image bounds the entropy of every pushed-forward law.",
        H("Finite Readout Alphabet Entropy Capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-readout-alphabet-entropy-capacity"),
                DeclarationHandle.Create(Declaration),
                H("A finite readout alphabet bounds pushed-forward entropy"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state space may be infinite. A PMF on that space is pushed forward "
                            + "along the canonical realizedReadout map into the actual range of "
                            + "the supplied readout.")),
                    Paragraph(Text(
                        "Finiteness is required only for the realized image. The real-valued law "
                            + "in the displayed formula is obtained by applying ENNReal.toReal to "
                            + "the pushed-forward PMF pointwise.")),
                    Paragraph(Text(
                        "The upper bound depends only on the cardinality of the realized image. "
                            + "No cardinality of an individual readout fiber occurs in either the "
                            + "hypothesis or the conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula prior = F.Id("P");
        Formula value = F.Id("y");
        Formula pmfMap = Seq(F.Id("PMF"), Dot, F.Id("map"));
        Formula image = Call("range", readout);
        Formula canonical = Apply(F.Id("realizedReadout"), readout);
        Formula pushed = Apply(pmfMap, canonical, prior);
        Formula realLaw = Seq(
            Open, Typed(value, image), Mapsto, Sp,
            Call("toReal", Apply(pushed, value)), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, output), type), Comma, RowBreak, Grp(),
            Typed(readout, Arrow(state, output)), Comma, RowBreak, Grp(),
            Call("Fintype", image), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(prior, Call("PMF", state)), Comma, RowBreak, Grp(),
            Call("H", realLaw), Sp, Le, Sp,
            Log, Open, Call("card", image), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
