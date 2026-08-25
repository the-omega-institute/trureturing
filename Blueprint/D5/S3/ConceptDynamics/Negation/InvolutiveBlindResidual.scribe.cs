using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class InvolutiveBlindResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hidden involutions generate blind residuals and primitive semantic escape.",
        H("Involutive Blind Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("structured-negation-generates-the-full-escape-chain"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Negation/InvolutiveBlindResidual."
                        + "structured_negation_escape_chain"),
                H("Structured negation generates the full escape chain"),
                StatementSource.FromAuthor(EscapeChainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume an inhabited source, an involutive negation hidden by the current "
                            + "readout and every definition in the old family, and Boolean target "
                            + "and candidate readouts that both negate along the same orbits.")),
                    Paragraph(Text(
                        "Any source point and its involutive partner agree for the current readout "
                            + "and the whole old family, while the negating target distinguishes "
                            + "them. That pair therefore inhabits the target blind residual.")),
                    Paragraph(Text(
                        "The negating candidate also distinguishes the pair, producing a "
                            + "productive separation. The accepted separation theorem then places "
                            + "the candidate outside the complete semantic closure of the old "
                            + "definition family.")),
                    Paragraph(Text(
                        "The conclusion packages exactly these three claims: nonempty blind "
                            + "residual, productive separation, and primitive escape. It does not "
                            + "assert escape without the hiddenness, negating, or inhabited-source "
                            + "hypotheses displayed in the antecedent."))),
                DescribeRole.Theorem))));

    private static Formula Concept(Formula state, Formula output) =>
        Call("Concept", state, output);

    private static Formula EscapeChainFormula()
    {
        Formula state = F.Id("X");
        Formula currentOutput = F.Id("Current");
        Formula inputOutput = F.Id("InputOutput");
        Formula negation = F.Id("negation");
        Formula family = F.Id("Gamma");
        Formula current = F.Id("current");
        Formula target = F.Id("target");
        Formula candidate = F.Id("candidate");
        Formula booleanConcept = Concept(state, F.Id("Bool"));

        Formula antecedent = Seq(
            Call("Nonempty", state), Sp, Land, Sp,
            Call("HiddenReadout", negation, current), Sp, Land, Sp,
            Call("FamilyHidden", negation, family), Sp, Land, RowBreak, Grp(),
            Call("NegatingReadout", negation, target), Sp, Land, Sp,
            Call("NegatingReadout", negation, candidate));

        Formula consequence = Seq(
            Call("Nonempty", Call("blindResidual", family, current, target)),
            Sp, Land, RowBreak, Grp(),
            Call("ProductiveSeparation", family, current, target, candidate),
            Sp, Land, RowBreak, Grp(),
            Call("PrimitiveEscape", family, candidate));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, negation, Colon, Sp,
            Call("InvolutiveNegation", state), Comma, RowBreak, Grp(),
            family, Colon, Sp,
            Call("Set", Concept(state, inputOutput)), Comma, RowBreak, Grp(),
            current, Colon, Sp, Concept(state, currentOutput), Comma, RowBreak, Grp(),
            target, Comma, Sp, candidate, Colon, Sp, booleanConcept,
            Comma, RowBreak, Grp(),
            Open, antecedent, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, consequence, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
