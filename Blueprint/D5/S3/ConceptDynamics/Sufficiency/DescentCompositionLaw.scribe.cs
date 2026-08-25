using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class DescentCompositionLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula Arrow(Formula domain, Formula codomain) =>
            new Formula.TypeArrow(domain, codomain);
        Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
        Formula Compose(Formula left, Formula right) => Seq(left, Sp, Circ, Sp, right);

        Formula state = F.Id("X");
        Formula intermediate = F.Id("B");
        Formula target = F.Id("C");
        Formula update = F.Id("F");
        Formula intermediateUpdate = F.Id("Fbar");
        Formula targetUpdate = F.Id("Ftilde");
        Formula firstReadout = F.Id("q");
        Formula secondReadout = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula compositeReadout = Compose(secondReadout, firstReadout);

        Formula statement = Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(state, Comma, Sp, intermediate, Comma, Sp, target), type),
                Comma),
            Seq(
                Typed(update, Arrow(state, state)), Comma, Sp,
                Typed(intermediateUpdate, Arrow(intermediate, intermediate)), Comma, Sp,
                Typed(targetUpdate, Arrow(target, target)), Comma),
            Seq(
                Typed(firstReadout, Arrow(state, intermediate)), Comma, Sp,
                Typed(secondReadout, Arrow(intermediate, target)), Comma),
            Seq(
                Compose(firstReadout, update), Sp, Eq, Sp,
                Compose(intermediateUpdate, firstReadout), Sp, Land, Sp,
                Compose(secondReadout, intermediateUpdate), Sp, Eq, Sp,
                Compose(targetUpdate, secondReadout), Sp, Rightarrow),
            Seq(
                Compose(compositeReadout, update), Sp, Eq, Sp,
                Compose(targetUpdate, compositeReadout), Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact descents through two successive readouts compose.",
            H("Descent Composition Law"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("successive-descents-compose"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/Sufficiency/DescentCompositionLaw."
                            + "descent_composition_law"),
                    H("Successive descents compose"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The first equation says that the readout q carries the state "
                                + "update F to the intermediate update Fbar. The second says "
                                + "that r carries Fbar to Ftilde.")),
                        Paragraph(Text(
                            "Substitution through the two commuting equations shows that the "
                                + "composite readout r after q carries F directly to Ftilde. "
                                + "No finiteness, topology, or inhabitedness assumption is used."))),
                    DescribeRole.Theorem))));
    }
}
