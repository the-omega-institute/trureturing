using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class LeastCommonRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quotient by the intersection relation is the least common refinement.",
        H("Least Common Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("least-common-refinement-has-a-unique-surjective-factor"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Fusion/LeastCommonRefinement."
                        + "least_common_refinement_universal_property"),
                H("The least common refinement has a unique surjective factor"),
                StatementSource.FromAuthor(UniversalPropertyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let R1 and R2 be equivalence relations on Y. A surjective projection "
                            + "r from Y onto W is assumed to admit surjective maps from W to "
                            + "both component quotients. Each map must commute with r and the "
                            + "corresponding canonical quotient projection.")),
                    Paragraph(Text(
                        "There is then a unique surjective map from W to the quotient of Y by "
                            + "the intersection of R1 and R2, and it commutes with the original "
                            + "projection. Thus the fused quotient retains exactly the least "
                            + "information needed to refine both component quotients.")),
                    Paragraph(Text(
                        "Compatibility puts every fiber of r inside both relations. A pinned "
                            + "Mathlib right inverse chooses a representative of each point of "
                            + "W; the intersection inclusion makes its fused class independent "
                            + "of that choice. Surjectivity of r proves both surjectivity and "
                            + "uniqueness of the induced map."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula QuotientOf(Formula relation) =>
        Seq(Operatorname, Grp(F.Id("Quotient")), Open, relation, Close);

    private static Formula ClassOf(Formula value, Formula relation) =>
        Seq(OpenBracket, value, CloseBracket, Underscore, Grp(relation));

    private static Formula UniversalPropertyFormula()
    {
        Formula yType = F.Id("Y");
        Formula wType = F.Id("W");
        Formula first = Seq(F.Id("R"), Underscore, Grp(D(1)));
        Formula second = Seq(F.Id("R"), Underscore, Grp(D(2)));
        Formula intersection = Call("inf", Seq(first, Comma, Sp, second));
        Formula projection = F.Id("r");
        Formula toFirst = Seq(F.Id("p"), Underscore, Grp(D(1)));
        Formula toSecond = Seq(F.Id("p"), Underscore, Grp(D(2)));
        Formula descend = F.Id("h");
        Formula y = F.Id("y");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, yType, Comma, Sp, wType, Comma, RowBreak,
            first, Comma, Sp, second, Colon, Sp,
            Operatorname, Grp(F.Id("Setoid")), Open, yType, Close, Comma, RowBreak,
            Typed(projection, new Formula.TypeArrow(yType, wType)), Comma, Sp,
            Typed(toFirst, new Formula.TypeArrow(wType, QuotientOf(first))), Comma, RowBreak,
            Typed(toSecond, new Formula.TypeArrow(wType, QuotientOf(second))), Comma, RowBreak,
            Call("Surjective", projection), Sp, Rightarrow, Sp,
            Call("Surjective", toFirst), Sp, Rightarrow, Sp,
            Call("Surjective", toSecond), Sp, Rightarrow, RowBreak,
            Open, Forall, Sp, y, InMacro, Sp, yType, Comma, Sp,
            Apply(toFirst, Apply(projection, y)), Sp, Eq, Sp,
            ClassOf(y, first), Close, Sp, Rightarrow, RowBreak,
            Open, Forall, Sp, y, InMacro, Sp, yType, Comma, Sp,
            Apply(toSecond, Apply(projection, y)), Sp, Eq, Sp,
            ClassOf(y, second), Close, Sp, Rightarrow, RowBreak,
            Exists, Bang, Sp, descend, Colon, Sp, wType, Sp, To, Sp,
            QuotientOf(intersection), Comma, Sp,
            Call("Surjective", descend), Sp, Land, RowBreak,
            Forall, Sp, y, InMacro, Sp, yType, Comma, Sp,
            Apply(descend, Apply(projection, y)), Sp, Eq, Sp,
            ClassOf(y, intersection), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
