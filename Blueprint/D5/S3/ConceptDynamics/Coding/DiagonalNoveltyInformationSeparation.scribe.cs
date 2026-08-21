using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class DiagonalNoveltyInformationSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal catalog escape need not strictly refine world-state information.",
        H("Diagonal Novelty and World Information"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-novelty-need-not-add-world-information"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/DiagonalNoveltyInformationSeparation."
                        + "diagonal_novelty_need_not_add_world_information"),
                H("Representational novelty need not add world information"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The expression address type, symbol type, world-state type, catalog, "
                            + "current world concept, and expression-semantics map are independent "
                            + "source primitives.")),
                    Paragraph(Text(
                        "The escaped expression is constructed by the canonical twisted diagonal "
                            + "of the supplied catalog. A fixed-point-free twist makes this "
                            + "expression absent from the catalog range.")),
                    Paragraph(Text(
                        "The second public clause has an independent premise: when the escaped "
                            + "expression's world semantics factors through the current concept, "
                            + "joining that semantic readout to the current concept cannot be a "
                            + "strict refinement.")),
                    Paragraph(Text(
                        "The first clause applies the frozen qualitative escape theorem. The "
                            + "second applies the frozen concept-join universal property to build "
                            + "the reverse factorization that contradicts strictness.")),
                    Paragraph(Text(
                        "Neither the expression semantics nor the current concept is defined from "
                            + "the non-strictness goal, so catalog novelty and world information "
                            + "remain distinct carriers."))),
                DescribeRole.Theorem))));

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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula address = F.Id("A");
        Formula symbolType = F.Id("Y");
        Formula world = F.Id("X");
        Formula currentType = Subscript(F.Id("B"), F.Id("C"));
        Formula expressionType = Subscript(F.Id("B"), F.Id("E"));
        Formula twist = F.Id("f");
        Formula catalog = F.Id("g");
        Formula current = F.Id("C");
        Formula semantics = F.Id("Sem");
        Formula symbol = F.Id("y");
        Formula escapedExpression = Call("diagonal", twist, catalog);
        Formula escapedSemantics = Apply(semantics, escapedExpression);
        Formula fixedPointFree = Seq(
            Forall, Sp, symbol, Comma, Sp,
            Apply(twist, symbol), Sp, Neq, Sp, symbol);
        Formula catalogEscape = Seq(
            Neg, Sp, Grp(escapedExpression, Sp, InMacro, Sp, Call("range", catalog)));
        Formula semanticNoGrowth = Seq(
            Call("Refines", escapedSemantics, current), Sp, Rightarrow, Sp,
            Neg, Sp, Call("StrictRefinement", current,
                Call("join", current, escapedSemantics)));
        Formula types = Seq(
            address, Comma, Sp, symbolType, Comma, Sp, world, Comma, Sp,
            currentType, Comma, Sp, expressionType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")));
        Formula primitives = Seq(
            twist, Colon, Sp, Arrow(symbolType, symbolType), Comma, Sp,
            catalog, Colon, Sp, Arrow(address, Arrow(address, symbolType)), Comma, RowBreak,
            Grp(), current, Colon, Sp, Arrow(world, currentType), Comma, Sp,
            semantics, Colon, Sp,
            Arrow(Seq(Open, Arrow(address, symbolType), Close),
                Arrow(world, expressionType)));

        return Disp(Seq(
            Forall, Sp, types, Comma, RowBreak, Grp(),
            primitives, Comma, RowBreak, Grp(),
            Grp(Open, fixedPointFree, Close, Sp, Rightarrow, Sp, catalogEscape),
            Sp, Land, RowBreak,
            Grp(), Grp(semanticNoGrowth), Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
