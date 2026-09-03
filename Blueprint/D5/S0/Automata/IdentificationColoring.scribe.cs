using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class IdentificationColoringDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A valid prefix-tree coloring is equivalent to a typed partial "
            + "DFAO together with certified reached states on every sample "
            + "prefix.",
        H("Typed DFAO Identification Colorings"),
        Blocks(Describe.Lean(
            DescribeId.Create("identification-machine-realization-equivalence"),
            DeclarationHandle.Create(
                "D5/S0/Automata/IdentificationColoring.identification_iff_machine_realization"),
            H("Identification certificates are equivalent to realized sample machines"),
            StatementSource.FromAuthor(EquivalenceFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An identification contains the finite color assignment, transition table, output labels, base-state types, and a reached-state proof for every prefix occurrence.")),
                Paragraph(Text(
                    "The equivalence permits later encoders to target either coloring data or typed-machine realization data while preserving the mathematical existence problem exactly."))),
            DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula EquivalenceFormula() => Disp(Seq(
        Call("Nonempty", Call("Identification", F.Id("S"), F.Id("B"), F.Id("C"))),
        Sp, Iff, Sp, Exists, Sp, F.Id("M"), Comma, Sp,
        Call("Nonempty", Call("PrefixRealization", F.Id("S"), F.Id("M"))),
        Sp, Land, Sp,
        Call("FitsSample", F.Id("S"), F.Id("M"))));
}
