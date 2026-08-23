using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class ExactDescentNoCarryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact descent through source and target readouts excludes every carry witness.",
        H("Exact Descent Has No Carry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-descent-has-no-carry"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry."
                        + "exact_descent_has_no_carry"),
                H("Exact descent excludes carry"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source readout, target readout, flow, and descended map are "
                            + "independent public primitives. Exact commutation is assumed, "
                            + "rather than installed by a definition.")),
                    Paragraph(Text(
                        "A carry is the existing family predicate: two states have the same "
                            + "source readout but different target readouts after the flow. "
                            + "Applying the descended map to the source equality contradicts "
                            + "the target inequality."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula targetState = F.Id("Y");
        Formula sourceReadout = F.Id("B");
        Formula targetReadout = F.Id("C");
        Formula qx = Seq(F.Id("q"), Underscore, Grp(state));
        Formula qy = Seq(F.Id("q"), Underscore, Grp(targetState));
        Formula flow = F.Id("F");
        Formula descended = Seq(Overline, Grp(flow));
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula targetFlow = Seq(qy, Sp, Circ, Sp, flow);
        Formula sourceIdentity = Seq(F.Id("id"), Underscore, Grp(state));
        Formula carry = Call(
            "IsCarryWitness", qx, sourceIdentity, Grp(targetFlow), left, right);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, targetState, Comma, Sp,
            sourceReadout, Comma, Sp, targetReadout, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            qx, Colon, Sp, Arrow(state, sourceReadout), Comma, Sp,
            qy, Colon, Sp, Arrow(targetState, targetReadout), Comma, RowBreak, Grp(),
            flow, Colon, Sp, Arrow(state, targetState), Comma, Sp,
            descended, Colon, Sp, Arrow(sourceReadout, targetReadout), Comma, RowBreak, Grp(),
            targetFlow, Sp, Eq, Sp, descended, Sp, Circ, Sp, qx,
            Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, left, Comma, Sp, right, InMacro, Sp, state, Comma, Sp,
            Neg, Sp, carry, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
