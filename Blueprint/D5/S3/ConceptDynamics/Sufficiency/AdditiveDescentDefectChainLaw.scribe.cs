using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class AdditiveDescentDefectChainLawDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula middleState = F.Id("Y");
        Formula targetState = F.Id("Z");
        Formula coordinate = F.Id("B");
        Formula sourceCoordinate = new Formula.Subscript(coordinate, F.Id("C"));
        Formula middleCoordinate = new Formula.Subscript(coordinate, F.Id("D"));
        Formula targetCoordinate = new Formula.Subscript(coordinate, F.Id("E"));
        Formula firstProcess = F.Id("F");
        Formula secondProcess = F.Id("G");
        Formula readout = F.Id("q");
        Formula sourceReadout = new Formula.Subscript(readout, F.Id("C"));
        Formula middleReadout = new Formula.Subscript(readout, F.Id("D"));
        Formula targetReadout = new Formula.Subscript(readout, F.Id("E"));
        Formula firstMacro = Seq(Overline, Grp(firstProcess));
        Formula secondMacro = Seq(Overline, Grp(secondProcess));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        Formula Compose(Formula left, Formula right) =>
            Seq(left, Sp, Circ, Sp, right);
        Formula Difference(Formula left, Formula right) =>
            Seq(Open, left, Sp, Minus, Sp, right, Close);

        Formula compositeDefect = Difference(
            Compose(Compose(targetReadout, secondProcess), firstProcess),
            Compose(Compose(secondMacro, firstMacro), sourceReadout));
        Formula secondDefectAtFirst = Compose(
            Difference(
                Compose(targetReadout, secondProcess),
                Compose(secondMacro, middleReadout)),
            firstProcess);
        Formula transportedFirstDefect = Compose(
            secondMacro,
            Difference(
                Compose(middleReadout, firstProcess),
                Compose(firstMacro, sourceReadout)));

        Formula statement = Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, middleState, Comma, Sp,
                targetState, Comma, Sp, sourceCoordinate, Comma, Sp,
                middleCoordinate, Comma, Sp, targetCoordinate, Colon, Sp, type,
                Comma),
            Seq(
                Grp(), OpenBracket, Call("AddGroup", middleCoordinate), CloseBracket,
                Comma, Sp,
                OpenBracket, Call("AddGroup", targetCoordinate), CloseBracket,
                Comma),
            Seq(
                firstProcess, Colon, Sp,
                new Formula.TypeArrow(state, middleState), Comma, Sp,
                secondProcess, Colon, Sp,
                new Formula.TypeArrow(middleState, targetState), Comma),
            Seq(
                sourceReadout, Colon, Sp,
                Call("Concept", state, sourceCoordinate), Comma, Sp,
                middleReadout, Colon, Sp,
                Call("Concept", middleState, middleCoordinate), Comma, Sp,
                targetReadout, Colon, Sp,
                Call("Concept", targetState, targetCoordinate), Comma),
            Seq(
                firstMacro, Colon, Sp,
                sourceCoordinate, Sp, To, Sp, middleCoordinate,
                Comma, Sp,
                secondMacro, Colon, Sp,
                Call("AddMonoidHom", middleCoordinate, targetCoordinate),
                Comma),
            Seq(
                compositeDefect, Sp, Eq, Sp,
                secondDefectAtFirst, Sp, Plus, Sp,
                transportedFirstDefect, Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Additive descent defects obey the composition chain law.",
            H("Additive Descent Defect Chain Law"),
            Blocks(Describe.Lean(
                DescribeId.Create("additive-descent-defect-chain-law"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Sufficiency/"
                        + "AdditiveDescentDefectChainLaw."
                        + "additive_descent_defect_chain_law"),
                H("Additive defects compose by a chain law"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three readouts and the two processes construct each defect "
                            + "directly as a difference of function composites. The first "
                            + "macroscopic map is arbitrary, while the second is additive "
                            + "because it transports the first defect.")),
                    Paragraph(Text(
                        "Expanding the two terms on the right makes the intermediate "
                            + "macroscopic readout cancel. Additive preservation of subtraction "
                            + "then leaves exactly the defect of the composite process."))),
                DescribeRole.Theorem))));
    }
}
