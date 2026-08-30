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
        Formula epsilon = Varepsilon;
        Formula firstDefectName = new Formula.Subscript(epsilon, Seq(firstProcess));
        Formula secondDefectName = new Formula.Subscript(epsilon, Seq(secondProcess));
        Formula compositeDefectName = new Formula.Subscript(
            epsilon,
            Seq(secondProcess, firstProcess));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula leftInput = F.Id("u");
        Formula rightInput = F.Id("v");

        Formula Compose(Formula left, Formula right) =>
            Seq(left, Sp, Circ, Sp, right);
        Formula Difference(Formula left, Formula right) =>
            Seq(Open, left, Sp, Minus, Sp, right, Close);

        Formula compositeDefect = Difference(
            Compose(Compose(targetReadout, secondProcess), firstProcess),
            Compose(Compose(secondMacro, firstMacro), sourceReadout));
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
                firstDefectName, Sp, Eq, Sp,
                Difference(
                    Compose(middleReadout, firstProcess),
                    Compose(firstMacro, sourceReadout)),
                Comma),
            Seq(
                secondDefectName, Sp, Eq, Sp,
                Difference(
                    Compose(targetReadout, secondProcess),
                    Compose(secondMacro, middleReadout)),
                Comma),
            Seq(
                compositeDefectName, Sp, Eq, Sp, compositeDefect,
                Comma),
            Seq(
                Forall, Sp, leftInput, Comma, Sp, rightInput,
                InMacro, Sp, middleCoordinate, Comma, Sp,
                secondMacro, Open, leftInput, Plus, rightInput, Close,
                Sp, Eq, Sp,
                secondMacro, Open, leftInput, Close, Plus,
                secondMacro, Open, rightInput, Close,
                Comma),
            Seq(
                compositeDefectName, Sp, Eq, Sp,
                Compose(secondDefectName, firstProcess), Sp, Plus, Sp,
                Compose(secondMacro, firstDefectName), Dot),
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
                        "The public definitions construct epsilon_F, epsilon_G, and epsilon_GF "
                            + "from the three readouts, two processes, and candidate macroscopic "
                            + "maps before the theorem relates those named objects.")),
                    Paragraph(Text(
                        "The source declares the second macroscopic map as an ordinary function, "
                            + "but the equation requires it to preserve addition and subtraction. "
                            + "Lean records that repair as an AddMonoidHom, and the displayed "
                            + "additivity equation makes the added scope explicit.")),
                    Paragraph(Text(
                        "After unfolding the named defects, the intermediate macroscopic readout "
                            + "cancels and preservation of subtraction leaves the composite defect."))),
                DescribeRole.Theorem))));
    }
}
