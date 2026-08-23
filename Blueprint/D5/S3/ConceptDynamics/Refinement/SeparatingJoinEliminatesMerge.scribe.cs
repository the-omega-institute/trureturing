using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class SeparatingJoinEliminatesMergeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concept that distinguishes two states removes their merge from the canonical "
            + "product refinement.",
        H("Separating Joins Eliminate Erroneous Merges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("separating-join-eliminates-merge"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/SeparatingJoinEliminatesMerge."
                        + "separating_join_eliminates_merge"),
                H("A separating coordinate eliminates the merged pair"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The current concept C and separating concept D are independent readouts "
                            + "on the same state carrier. Their refinement is the frozen canonical "
                            + "conceptJoin, which maps x to the product coordinate (C(x), D(x)).")),
                    Paragraph(Text(
                        "If D gives x and y different coordinates, equality of their joined "
                            + "coordinates would force equality in the second product component. "
                            + "Therefore the specific erroneous merge, and hence that concrete "
                            + "pseudo-witness, is absent after refinement.")),
                    Paragraph(Text(
                        "The proof imports the family concept and join primitives and applies "
                            + "pinned Mathlib's Prod.mk.injEq directly; no replacement join or "
                            + "target-defined object is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula currentType = new Formula.Subscript(F.Id("B"), F.Id("C"));
        Formula separatingType = new Formula.Subscript(F.Id("B"), F.Id("D"));
        Formula current = F.Id("C");
        Formula separating = F.Id("D");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula join = Call("conceptJoin", current, separating);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, currentType, Comma, Sp,
            separatingType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            current, Colon, Sp, Arrow(state, currentType), Comma, Sp,
            separating, Colon, Sp, Arrow(state, separatingType), Comma, Sp,
            x, Comma, Sp, y, Colon, Sp, state, Comma,
            RowBreak, Grp(),
            Apply(separating, x), Sp, Neq, Sp, Apply(separating, y),
            Sp, Rightarrow, Sp,
            Apply(join, x), Sp, Neq, Sp, Apply(join, y), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
