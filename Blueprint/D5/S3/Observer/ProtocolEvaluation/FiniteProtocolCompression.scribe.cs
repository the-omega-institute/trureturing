using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProtocolEvaluation;

internal sealed class FiniteProtocolCompressionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/ProtocolEvaluation/FiniteProtocolCompression."
            + "finite_protocol_subfamily_card_le_quotient_card_sub_one";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite protocol quotient has an exact certificate with at most one fewer protocols than classes.",
        H("Finite Protocol Compression"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-protocol-compression"),
            DeclarationHandle.Create(Declaration),
            H("Finite quotients admit sharp protocol certificates"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite state carrier, let K(Q) be equality of all evaluation "
                        + "readouts indexed by the available protocol family Q. The quotient "
                        + "is the actual quotient of the state carrier by this kernel.")),
                Paragraph(Text(
                    "There is a finite selected protocol family contained in Q whose kernel "
                        + "equals K(Q), and its cardinality is at most the number of quotient "
                        + "classes minus one."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula protocol = F.Id("Protocol");
        Formula state = F.Id("State");
        Formula observation = F.Id("Observation");
        Formula available = F.Id("Q");
        Formula evaluation = F.Id("e");
        Formula selected = F.Id("Q0");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula selectedKernel = Call(
            "experimentIndistinguishability", selected, evaluation);
        Formula availableKernel = Call(
            "experimentIndistinguishability", available, evaluation);
        Formula quotient = Call("ProtocolQuotient", available, evaluation);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(
                    Seq(protocol, Comma, Sp, state, Comma, Sp, observation),
                    type),
                Comma),
            Seq(
                Grp(), Finite(state), Comma, Sp,
                Typed(available, Call("Set", protocol)), Comma, Sp,
                Typed(
                    evaluation,
                    Arrow(protocol, Arrow(state, observation))),
                Comma),
            Seq(
                Grp(), Exists, Sp,
                Typed(selected, Call("Finset", protocol)), Comma),
            Seq(
                Grp(), Call("subset", selected, available), Sp, Land),
            Seq(
                Grp(), selectedKernel, Sp, Eq, Sp, availableKernel, Sp, Land),
            Seq(
                Grp(), Call("card", selected), Sp, Leq, Sp,
                Call("card", quotient), Sp, Minus, Sp, D(1), Dot),
        ]));
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Finite(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, carrier, CloseBracket);

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
}
