using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentBoundary;

internal sealed class ProtocolInnovationCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A protocol is innovative exactly when it separates a current observation fiber.",
        H("Protocol Innovation Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("protocol-innovation-separates-current-fiber"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ExperimentBoundary/ProtocolInnovationCriterion."
                        + "protocol_innovation_iff_separates_current_fiber"),
                H("Protocol innovation is an explicit fiber separation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The current protocol and the added protocol law are source readouts. "
                            + "Their canonical concept join records both values without "
                            + "introducing a parallel completion object.")),
                    Paragraph(Text(
                        "The joined kernel is a proper subset of the current kernel exactly "
                            + "when two currently indistinguishable states receive different "
                            + "values from the added protocol law."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula currentValue = F.Id("P");
        Formula lawValue = F.Id("Y");
        Formula current = F.Id("q");
        Formula law = F.Id("L");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula joinedKernel = Call("ker", Call("conceptJoin", current, law));
        Formula currentKernel = Call("ker", current);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            state, Comma, Sp, currentValue, Comma, Sp, lawValue,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            current, Colon, Sp, new Formula.TypeArrow(state, currentValue),
            Comma, Sp,
            law, Colon, Sp, new Formula.TypeArrow(state, lawValue),
            Comma, RowBreak, Grp(),
            joinedKernel, Sp, Subset, Sp, currentKernel,
            Sp, Iff, Sp, RowBreak, Grp(),
            Exists, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Apply(current, x), Sp, Eq, Sp, Apply(current, y),
            Sp, Land, Sp,
            Apply(law, x), Sp, Neq, Sp, Apply(law, y), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
