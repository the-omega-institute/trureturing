using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ContextRefinementConflictSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A refinement separates opposite support hidden by one coarse context.",
        H("Context Refinement Separates a Coarse Conflict"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("context-refinement-separates-coarse-conflict"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ContextRefinementConflictSeparation."
                        + "context_refinement_separates_conflict"),
                H("Refinement separates opposite support into distinct contexts"),
                StatementSource.FromAuthor(ConflictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coarse and refinement contexts are the canonical concept readouts. "
                            + "The joined context is constructed with the existing product readout, "
                            + "so this theorem extends the family source of truth.")),
                    Paragraph(Text(
                        "All four source clauses are public: joined-fiber separation, exclusion "
                            + "from one joined context, positive and negative support in distinct "
                            + "refinement coordinates, and their shared coarse coordinate.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no theorem combining fiber "
                            + "separation with opposite predicate support. The proof applies the "
                            + "canonical conceptJoin and product projection directly."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ConflictFormula()
    {
        Formula source = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula coarse = Subscript(F.Id("q"), coarseType);
        Formula fine = Subscript(F.Id("q"), fineType);
        Formula support = F.Id("P");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula joinedContext = F.Id("b");
        Formula coarseContext = F.Id("c");
        Formula positiveContext = Subscript(F.Id("d"), F.Id("p"));
        Formula negativeContext = Subscript(F.Id("d"), F.Id("n"));
        Formula joinX = Call("conceptJoin", coarse, fine, x);
        Formula joinY = Call("conceptJoin", coarse, fine, y);
        Formula positive = Apply(support, x);
        Formula negative = Seq(Neg, Sp, Apply(support, y));
        Formula hypotheses = Seq(
            Apply(coarse, x), Sp, Eq, Sp, Apply(coarse, y), Sp, Land, Sp,
            positive, Sp, Land, Sp, negative, Sp, Land, Sp,
            Apply(fine, x), Sp, Neq, Sp, Apply(fine, y));
        Formula noSharedJoinedContext = Seq(
            Neg, Sp, Exists, Sp, joinedContext, Colon, Sp,
            coarseType, Sp, Times, Sp, fineType, Comma, Sp,
            joinX, Sp, Eq, Sp, joinedContext, Sp, Land, Sp,
            positive, Sp, Land, Sp,
            joinY, Sp, Eq, Sp, joinedContext, Sp, Land, Sp, negative);
        Formula distinctRefinementContexts = Seq(
            Exists, Sp, positiveContext, Comma, Sp, negativeContext,
            Colon, Sp, fineType, Comma, Sp,
            positiveContext, Sp, Neq, Sp, negativeContext, Sp, Land, Sp,
            Apply(fine, x), Sp, Eq, Sp, positiveContext, Sp, Land, Sp,
            positive, Sp, Land, Sp,
            Apply(fine, y), Sp, Eq, Sp, negativeContext, Sp, Land, Sp, negative);
        Formula coarseConflict = Seq(
            Exists, Sp, coarseContext, Colon, Sp, coarseType, Comma, Sp,
            Exists, Sp, positiveContext, Comma, Sp, negativeContext,
            Colon, Sp, fineType, Comma, Sp,
            positiveContext, Sp, Neq, Sp, negativeContext, Sp, Land, Sp,
            Apply(coarse, x), Sp, Eq, Sp, coarseContext, Sp, Land, Sp,
            Apply(fine, x), Sp, Eq, Sp, positiveContext, Sp, Land, Sp,
            positive, Sp, Land, Sp,
            Apply(coarse, y), Sp, Eq, Sp, coarseContext, Sp, Land, Sp,
            Apply(fine, y), Sp, Eq, Sp, negativeContext, Sp, Land, Sp, negative);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coarseType, Comma, Sp, fineType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            coarse, Colon, Sp, Arrow(source, coarseType), Comma, Sp,
            fine, Colon, Sp, Arrow(source, fineType), Comma, Sp,
            support, Colon, Sp, Arrow(source, Seq(Operatorname, Grp(F.Id("Prop")))), Comma, Esc,
            x, Comma, Sp, y, Colon, Sp, source, Comma, Esc,
            hypotheses, Sp, Rightarrow, Esc,
            Open,
            Open, joinX, Sp, Neq, Sp, joinY, Close, Sp, Land, Esc,
            Open, noSharedJoinedContext, Close, Sp, Land, Esc,
            Open, distinctRefinementContexts, Close, Sp, Land, Esc,
            Open, coarseConflict, Close,
            Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
