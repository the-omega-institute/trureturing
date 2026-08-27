using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class DoubleExtensionalEvaluationDescentDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evaluation descends canonically through its row and column kernels.",
        H("Double Extensional Evaluation Descent"),
        Blocks(Describe.Lean(
            DescribeId.Create("double-extensional-evaluation-descent"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Refinement/DoubleExtensionalEvaluationDescent."
                    + "double_extensional_evaluation_descent"),
            H("The double quotient evaluation is representative-independent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary evaluation table, the state relation is constructed by "
                        + "equality of complete evaluation rows and the protocol relation by "
                        + "equality of complete evaluation columns.")),
                Paragraph(Text(
                    "Simultaneous relatedness in those two kernels forces equal evaluation "
                        + "values. The pinned quotient lift therefore constructs the displayed "
                        + "map on the two canonical quotient carriers.")),
                Paragraph(Text(
                    "The computation rule states representative independence directly. "
                        + "Surjectivity of both quotient projections also makes this canonical "
                        + "map unique among all maps with the same rule.")),
                Paragraph(Text(
                    "Repository searches found application-specific quotient metrics and "
                        + "predictive descents, but no existing joint row-and-column evaluation "
                        + "descent."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula protocol = F.Id("Protocol");
        Formula value = F.Id("Value");
        Formula evaluation = F.Id("e");
        Formula stateKernel = new Formula.Subscript(F.Id("K"), state);
        Formula protocolKernel = new Formula.Subscript(F.Id("K"), protocol);
        Formula descended = Seq(Overline, Grp(evaluation));
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula other = F.Id("f");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula evaluationType = Arrow(state, Arrow(protocol, value));
        Formula stateQuotient = Call("Quotient", stateKernel);
        Formula protocolQuotient = Call("Quotient", protocolKernel);
        Formula descendedType = Arrow(stateQuotient, Arrow(protocolQuotient, value));
        Formula stateKernelConstruction = Seq(
            stateKernel, Sp, Eq, Sp, Ker, Open,
            LambdaLower, Sp, Typed(x, state), Comma, Sp,
            LambdaLower, Sp, Typed(p, protocol), Comma, Sp,
            Apply(evaluation, x, p), Close);
        Formula protocolKernelConstruction = Seq(
            protocolKernel, Sp, Eq, Sp, Ker, Open,
            LambdaLower, Sp, Typed(p, protocol), Comma, Sp,
            LambdaLower, Sp, Typed(x, state), Comma, Sp,
            Apply(evaluation, x, p), Close);
        Formula descendedConstruction = Seq(
            descended, Colon, Sp, descendedType, Sp, Eq, Sp,
            Call("liftOn2", evaluation, stateKernel, protocolKernel));
        Formula representativeInvariant = Seq(
            Forall, Sp, Typed(Seq(x, Comma, Sp, y), state), Comma, Sp,
            Typed(Seq(p, Comma, Sp, q), protocol), Comma, Sp,
            Call(stateKernel, x, y), Sp, Land, Sp,
            Call(protocolKernel, p, q), Sp, Rightarrow, Sp,
            Apply(evaluation, x, p), Sp, Eq, Sp, Apply(evaluation, y, q));
        Formula computation = Seq(
            Forall, Sp, Typed(x, state), Comma, Sp, Typed(p, protocol), Comma, Sp,
            Apply(descended, Call("class", x), Call("class", p)), Sp, Eq, Sp,
            Apply(evaluation, x, p));
        Formula uniqueness = Seq(
            Forall, Sp, Typed(other, descendedType), Comma, Sp,
            Open, Forall, Sp, Typed(x, state), Comma, Sp, Typed(p, protocol), Comma, Sp,
            Apply(other, Call("class", x), Call("class", p)), Sp, Eq, Sp,
            Apply(evaluation, x, p), Close, Sp, Rightarrow, Sp,
            other, Sp, Eq, Sp, descended);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, protocol, Comma, Sp, value), type),
            Comma, RowBreak, Grp(),
            Forall, Sp, Typed(evaluation, evaluationType), Comma,
            RowBreak, Grp(), stateKernelConstruction, Comma,
            RowBreak, Grp(), protocolKernelConstruction, Comma,
            RowBreak, Grp(), descendedConstruction, Comma,
            RowBreak, Grp(), Open, representativeInvariant, Close, Sp, Land,
            RowBreak, Grp(), Open, computation, Close, Sp, Land,
            RowBreak, Grp(), Open, uniqueness, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Typed(Formula expression, Formula type) =>
        Seq(expression, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        Seq(function, Open, Join(arguments), Close);

    private static Formula Join(Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq([.. items]);
    }

    private static Formula Call(Formula name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(name), Open, Join(arguments), Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);
}
