using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class MisleadingReceiverExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorized targets and image-correct decoding exclude misleading reception.",
        H("Misleading Receiver Exclusion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("misleading-impossible"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/MisleadingReceiverExclusion."
                        + "misleading_impossible"),
                H("Misleading reception is impossible under correct image decoding"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M_S map an actual state to its message, let T be the target "
                            + "value, let d be the correct decoder, and let delta be the "
                            + "receiver's decoder. A receiver is misleading at state a exactly "
                            + "when delta(M_S(a)) differs from T(a).")),
                    Paragraph(Text(
                        "If the target factors as T = d composed with M_S and delta agrees with "
                            + "d on the actual message image, then every actual message decodes "
                            + "to its target. Thus no state is misleading."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("A");
        Formula message = F.Id("M");
        Formula target = F.Id("Y");
        Formula messageOf = new Formula.Subscript(F.Id("M"), F.Id("S"));
        Formula correct = F.Id("d");
        Formula receiver = F.Id("delta");
        Formula stateValue = F.Id("a");
        Formula messageValue = F.Id("m");
        Formula factorization = Seq(
            F.Id("T"), Sp, Eq, Sp, correct, Sp, Circ, Sp, messageOf);
        Formula agreement = Seq(
            Forall, Sp, messageValue, Comma, Sp,
            messageValue, Sp, InMacro, Sp, Call("range", messageOf), Sp,
            Rightarrow, Sp, At(receiver, messageValue), Sp, Eq, Sp,
            At(correct, messageValue));
        Formula misleading = Seq(
            Call("Misleading", messageOf, F.Id("T"), receiver, stateValue));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            state, Comma, Sp, message, Comma, Sp, target, Comma, RowBreak, Grp(),
            messageOf, Colon, Sp, state, Sp, To, Sp, message, Comma, Sp,
            F.Id("T"), Colon, Sp, state, Sp, To, Sp, target, Comma, Sp,
            receiver, Colon, Sp, message, Sp, To, Sp, target, Comma, Sp,
            correct, Colon, Sp, message, Sp, To, Sp, target, Comma, RowBreak, Grp(),
            factorization, Comma, RowBreak, Grp(),
            agreement, Comma, RowBreak, Grp(),
            Forall, Sp, stateValue, Comma, Sp, Neg, misleading, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
