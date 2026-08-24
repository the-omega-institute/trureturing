using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class GlobalFrameCoboundaryCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula index = F.Id("I");
        Formula baseType = F.Id("X");
        Formula unitGroup = F.Id("U");
        Formula overlap = F.Id("overlap");
        Formula transition = F.Id("g");
        Formula coefficients = F.Id("a");
        Formula localUnit = F.Id("h");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));

        Formula transitionAt = ApplyIndexed(transition, Seq(i, Comma, Sp, j), x);
        Formula coefficientAtI = ApplyIndexed(coefficients, i, x);
        Formula coefficientAtJ = ApplyIndexed(coefficients, j, x);
        Formula localUnitAtI = ApplyIndexed(localUnit, i, x);
        Formula localUnitAtJ = ApplyIndexed(localUnit, j, x);
        Formula inverseAtI = Seq(localUnitAtI, Caret, Grp(Seq(Minus, D(1))));

        Formula compatibleFrame = Seq(
            Exists, Sp, coefficients, Colon, Sp,
            index, Sp, To, Sp, baseType, Sp, To, Sp, unitGroup, Comma, RowBreak,
            Grp(), Forall, Sp, i, Comma, Sp, j, Comma, Sp, x, Comma, Sp,
            Call("overlap", i, j, x), Sp, Rightarrow, Sp,
            coefficientAtI, Sp, Eq, Sp,
            transitionAt, Sp, coefficientAtJ);

        Formula coboundary = Seq(
            Exists, Sp, localUnit, Colon, Sp,
            index, Sp, To, Sp, baseType, Sp, To, Sp, unitGroup, Comma, RowBreak,
            Grp(), Forall, Sp, i, Comma, Sp, j, Comma, Sp, x, Comma, Sp,
            Call("overlap", i, j, x), Sp, Rightarrow, Sp,
            transitionAt, Sp, Eq, Sp, inverseAtI, Sp, localUnitAtJ);

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Comma, Sp, baseType, Comma, Sp, unitGroup,
            Colon, Sp, universe, Comma, RowBreak, Grp(),
            OpenBracket, Call("Group", unitGroup), CloseBracket, Comma, RowBreak, Grp(),
            overlap, Colon, Sp, index, Sp, To, Sp, index, Sp, To, Sp,
            baseType, Sp, To, Sp, proposition, Comma, RowBreak, Grp(),
            transition, Colon, Sp, index, Sp, To, Sp, index, Sp, To, Sp,
            baseType, Sp, To, Sp, unitGroup, Comma, RowBreak, Grp(),
            Open, compatibleFrame, Close, Sp, Iff, RowBreak, Grp(),
            Open, coboundary, Close, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A nonvanishing frame descends from local bases exactly when their unit-valued "
                + "transition data is a coboundary.",
            H("Global Frame Coboundary Criterion"),
            Blocks(Describe.Lean(
                DescribeId.Create("global-frame-iff-transition-coboundary"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion."
                        + "global_frame_iff_transition_coboundary"),
                H("A global frame exists exactly for coboundary transition data"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The overlap predicate specifies where two local trivializations meet. "
                            + "All displayed coefficient values lie in a group of units, so "
                            + "they represent nonvanishing rescalings of the chosen local "
                            + "bases. Compatibility is stated directly on every overlap.")),
                    Paragraph(Text(
                        "From compatible frame coefficients a, take h_i to be the pointwise "
                            + "inverse of a_i. Right cancellation then gives "
                            + "g_ij = h_i^{-1} h_j. Conversely, rescale the i-th local basis by "
                            + "h_i^{-1}; the coboundary equation makes these rescaled bases "
                            + "agree on every overlap.")),
                    Paragraph(Text(
                        "This is the algebraic descent carrier of the criterion. It is pointwise "
                            + "in the base and therefore applies to unit-valued local functions; "
                            + "no topology-specific regularity assertion is added."))),
                DescribeRole.Theorem))));
    }

    private static Formula ApplyIndexed(Formula function, Formula subscript, Formula argument) =>
        Seq(new Formula.Subscript(function, subscript), Open, argument, Close);
}
