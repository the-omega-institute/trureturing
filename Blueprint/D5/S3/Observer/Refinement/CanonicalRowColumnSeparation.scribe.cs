using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class CanonicalRowColumnSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical row-column behavioral quotient separates both axes.",
        H("Canonical Row-Column Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-row-column-separation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Refinement/CanonicalRowColumnSeparation."
                        + "canonical_row_column_separation"),
                H("The behavioral double quotient separates rows and columns"),
                StatementSource.FromAuthor(CollapseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state row and protocol column are constructed directly from the "
                            + "evaluation channel e. Their equality kernels define the two "
                            + "canonical quotient carriers.")),
                    Paragraph(Text(
                        "The displayed descended evaluation is the canonical two-variable "
                            + "quotient lift of e. Equality on all quotient protocols forces "
                            + "equal state rows, hence equal state classes; the protocol proof "
                            + "is the symmetric argument.")),
                    Paragraph(Text(
                        "No representative selector or choice of quotient section is used."))),
                DescribeRole.Theorem))));

    private static Formula Type() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Named(string name, params Formula[] arguments)
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

    private static Formula CollapseFormula()
    {
        Formula state = F.Id("X");
        Formula protocol = F.Id("P");
        Formula response = Lambda;
        Formula evaluation = F.Id("e");
        Formula row = F.Id("r");
        Formula column = F.Id("c");
        Formula stateQuotient = Seq(Overline, Grp(state));
        Formula protocolQuotient = Seq(Overline, Grp(protocol));
        Formula descended = Seq(Overline, Grp(evaluation));
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula test = F.Id("q");
        Formula rowDefinition = Seq(
            row, Colon, Sp, Arrow(state, Arrow(protocol, response)), Sp, Colon, Sp, Eq, Sp,
            LambdaLower, Sp, x, Sp, p, Comma, Sp, Apply(evaluation, x, p));
        Formula columnDefinition = Seq(
            column, Colon, Sp, Arrow(protocol, Arrow(state, response)), Sp, Colon, Sp, Eq, Sp,
            LambdaLower, Sp, p, Sp, x, Comma, Sp, Apply(evaluation, x, p));
        Formula stateQuotientDefinition = Seq(
            stateQuotient, Sp, Colon, Sp, Eq, Sp,
            Named("Quotient", Named("ker", row)));
        Formula protocolQuotientDefinition = Seq(
            protocolQuotient, Sp, Colon, Sp, Eq, Sp,
            Named("Quotient", Named("ker", column)));
        Formula descendedDefinition = Seq(
            descended, Colon, Sp, Arrow(stateQuotient, Arrow(protocolQuotient, response)),
            Sp, Colon, Sp, Eq, Sp, Named("QuotientLift2", evaluation, Named("ker", row),
                Named("ker", column)));
        Formula stateSeparation = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, stateQuotient, Comma, Sp,
            Open, Forall, Sp, test, Colon, Sp, protocolQuotient, Comma, Sp,
            Apply(descended, first, test), Sp, Eq, Sp,
            Apply(descended, second, test), Close, Sp, Rightarrow, Sp,
            first, Sp, Eq, Sp, second);
        Formula protocolSeparation = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, protocolQuotient, Comma, Sp,
            Open, Forall, Sp, test, Colon, Sp, stateQuotient, Comma, Sp,
            Apply(descended, test, first), Sp, Eq, Sp,
            Apply(descended, test, second), Close, Sp, Rightarrow, Sp,
            first, Sp, Eq, Sp, second);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, protocol, Comma, Sp, response,
            Colon, Sp, Type(), Comma,
            RowBreak, Grp(),
            evaluation, Colon, Sp, Arrow(state, Arrow(protocol, response)), Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp, rowDefinition, Comma,
            RowBreak, Grp(),
            columnDefinition, Comma,
            RowBreak, Grp(),
            stateQuotientDefinition, Comma, Sp, protocolQuotientDefinition, Comma,
            RowBreak, Grp(),
            descendedDefinition, Sp, Operatorname, Grp(F.Id("in")),
            RowBreak, Grp(),
            Open, stateSeparation, Close, Sp, Land,
            RowBreak, Grp(),
            Open, protocolSeparation, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
