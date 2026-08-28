using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class FiniteFaithfulSubfamilyExtractionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/FiniteFaithfulSubfamilyExtraction."
            + "finite_faithful_subfamily_extraction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful observer family on a finite state carrier contains a faithful finite "
            + "subfamily.",
        H("Finite Extraction of a Faithful Observer Family"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-faithful-observer-subfamily-extraction"),
            DeclarationHandle.Create(Declaration),
            H("Full joint faithfulness is witnessed by finitely many coordinates"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The full observer is the canonical dependent joint readout of the "
                        + "coordinate family. Its injectivity means every distinct pair of "
                        + "states is separated by at least one coordinate.")),
                Paragraph(Text(
                    "There are only finitely many distinct state pairs. A finite-subcover "
                        + "argument selects finitely many separating coordinates, and their "
                        + "restricted dependent joint readout remains injective."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula indexType = F.Id("I");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula index = F.Id("i");
        Formula selected = F.Id("J");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula finiteState = Seq(
            OpenBracket, Call("Finite", state), CloseBracket);
        Formula dependentReadoutType = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            state, Sp, To, Sp, Apply(output, index));
        Formula selectedIndex = Seq(
            OpenBrace, index, Colon, Sp, indexType, Sp, Mid, Sp,
            index, Sp, InMacro, Sp, selected, CloseBrace);
        Formula selectedReadout = Grp(
            index, Colon, Sp, selectedIndex, Sp, Mapsto, Sp,
            Apply(readout, index));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, indexType, Colon, Sp, type,
                Comma, Sp, output, Colon, Sp, indexType, Sp, To, Sp, type,
                Comma),
            Seq(
                Grp(), finiteState, Comma, Sp, readout, Colon, Sp,
                dependentReadoutType, Comma),
            Seq(
                Call("Injective", Call("jointReadout", readout)), Sp, Implies),
            Seq(
                Exists, Sp, selected, Colon, Sp, Call("Finset", indexType),
                Comma, Sp,
                Call("Injective", Call("jointReadout", selectedReadout)), Dot),
        ]));
    }

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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
