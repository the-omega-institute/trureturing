using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FiberBinaryIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary binary questions identify finite fiber targets at logarithmic depth.",
        H("Binary Identification within Concept Fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arbitrary-binary-questions-identify-fiber-targets"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification."
                        + "arbitrary_binary_questions_identify_target"),
                H("Arbitrary binary questions identify every finite fiber target"),
                StatementSource.FromAuthor(IdentificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite current concept readout and finite target, fiber target "
                            + "diversity counts the distinct target values realized at one "
                            + "coordinate. Worst fiber diversity is the finite maximum of those "
                            + "counts, with empty coordinate carriers contributing zero.")),
                    Paragraph(Text(
                        "A binary protocol is indexed by its finite depth. At each round it "
                            + "selects a binary concept readout from the complete preceding bit "
                            + "history, and its transcript carries a consistency proof for all "
                            + "states and rounds.")),
                    Paragraph(Text(
                        "The public existential returns such a protocol at exactly the ceiling "
                            + "binary-logarithm depth. Identification is direct: equal current "
                            + "coordinates and equal complete transcripts force equal targets.")),
                    Paragraph(Text(
                        "The construction assigns an injective fixed-length bit vector to every "
                            + "target value realized in each fiber. The pinned natural logarithm "
                            + "bound supplies enough bit vectors, and the selected questions ask "
                            + "their bits in order."))),
                DescribeRole.Theorem))));

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

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula IdentificationFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("C");
        Formula targetCarrier = F.Id("Target");
        Formula current = new Formula.Subscript(F.Id("q"), coordinate);
        Formula target = F.Id("T");
        Formula protocol = F.Id("pi");
        Formula diversity = Call("worstFiberDiversity", current, target);
        Formula depth = Call("clog", D(2), diversity);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coordinate, Comma, Sp, targetCarrier,
            Comma, RowBreak, Grp(),
            Fintype(state), Sp, Fintype(coordinate), Sp, Fintype(targetCarrier),
            Comma, RowBreak, Grp(),
            current, Colon, Sp, state, Sp, To, Sp, coordinate, Comma, Sp,
            target, Colon, Sp, state, Sp, To, Sp, targetCarrier, Comma,
            RowBreak, Grp(),
            Exists, Sp, protocol, Colon, Sp,
            Call("BinaryProtocol", state, depth), Comma, RowBreak, Grp(),
            Call("IdentifiesGiven", current, target, protocol), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
