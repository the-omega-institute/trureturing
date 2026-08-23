using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Lawvere;

internal sealed class TheoryIsConsequenceFixedPointDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S0/Diagonal/Lawvere/TheoryIsConsequenceFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deductively closed sets are precisely the fixed points of consequence closure, whose fixed points form a complete lattice under intersections.",
        H("Theories as Consequence Fixed Points"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("theories-are-exactly-consequence-fixed-points"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "theory_iff_consequence_fixedPoint"),
                H("Theories are exactly consequence fixed points"),
                StatementSource.FromAuthor(TheoryIffFixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A theory contains every consequence generated from itself. Since a "
                            + "closure operator is extensive, the reverse inclusion already "
                            + "holds, so deductive closure is equivalent to equality with the "
                            + "consequence closure.")),
                    Paragraph(Text(
                        "Thus the theories of an arbitrary Tarskian consequence operator are "
                            + "exactly its fixed points. The statement uses only the closure "
                            + "laws and imposes no finiteness condition on formulas or theories."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("consequence-closure-is-a-fixed-point"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "consequenceClosure_is_fixedPoint"),
                H("Consequence closure is a fixed point"),
                StatementSource.FromAuthor(ClosureIsFixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Closing any set of formulas produces a deductively closed set. Applying "
                            + "the same consequence operator again changes nothing, by the "
                            + "idempotence law for closure operators."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("consequence-closure-is-least-above-generators"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "consequenceClosure_isLeast_fixedPoint_above"),
                H("Consequence closure is least above its generators"),
                StatementSource.FromAuthor(ClosureIsLeastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The closure of a generating set contains every generator and is itself "
                            + "a fixed point. If another fixed point contains the generators, "
                            + "closure minimality places the generated closure inside it.")),
                    Paragraph(Text(
                        "Consequently the deductive closure is the least closed theory extending "
                            + "the chosen assumptions, not merely one closed extension among many."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fixed-points-are-closed-under-arbitrary-intersections"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "fixedPoints_closed_under_sInf"),
                H("Fixed points are closed under arbitrary intersections"),
                StatementSource.FromAuthor(FixedPointsClosedUnderIntersectionsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The intersection of any family of consequence fixed points is again a "
                            + "fixed point. No nonemptiness assumption is needed: closed sets of "
                            + "a closure operator are preserved by arbitrary infima.")),
                    Paragraph(Text(
                        "Together with the inherited order, this intersection law supplies the "
                            + "meet structure behind the complete lattice of theories."))),
                DescribeRole.Lemma))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula SetOf(Formula element) =>
        Call("Set", element);

    private static Formula ConsequenceOperatorOf(Formula element) =>
        Call("ConsequenceOperator", element);

    private static Formula FixedPointsOf(Formula consequence) =>
        Call("fixedPoints", consequence);

    private static Formula ClosureOf(Formula set) =>
        Call("Cn", set);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula IsFixedPoint(Formula value, Formula consequence) =>
        Seq(value, Sp, InMacro, Sp, FixedPointsOf(consequence));

    private static Formula TheoryIffFixedPointFormula()
    {
        Formula formula = F.Id("Formula");
        Formula consequence = F.Id("Cn");
        Formula theory = F.Id("S");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(formula, TypeUniverse()), Comma, RowBreak, Grp(),
            Typed(consequence, ConsequenceOperatorOf(formula)), Comma, Sp,
            Typed(theory, SetOf(formula)), Comma, RowBreak, Grp(),
            Call("IsTheory", consequence, theory), Sp, Iff, Sp,
            IsFixedPoint(theory, consequence), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ClosureIsFixedPointFormula()
    {
        Formula formula = F.Id("Formula");
        Formula consequence = F.Id("Cn");
        Formula generators = F.Id("S");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(formula, TypeUniverse()), Comma, RowBreak, Grp(),
            Typed(consequence, ConsequenceOperatorOf(formula)), Comma, Sp,
            Typed(generators, SetOf(formula)), Comma, RowBreak, Grp(),
            IsFixedPoint(ClosureOf(generators), consequence), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ClosureIsLeastFormula()
    {
        Formula formula = F.Id("Formula");
        Formula consequence = F.Id("Cn");
        Formula generators = F.Id("S");
        Formula candidate = F.Id("T");
        Formula candidates = Seq(
            OpenBrace,
            Typed(candidate, SetOf(formula)), Sp, Mid, Sp,
            generators, Sp, Subseteq, Sp, candidate, Sp, Land, Sp,
            IsFixedPoint(candidate, consequence),
            CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(formula, TypeUniverse()), Comma, RowBreak, Grp(),
            Typed(consequence, ConsequenceOperatorOf(formula)), Comma, Sp,
            Typed(generators, SetOf(formula)), Comma, RowBreak, Grp(),
            Call("IsLeast", candidates, ClosureOf(generators)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FixedPointsClosedUnderIntersectionsFormula()
    {
        Formula formula = F.Id("Formula");
        Formula consequence = F.Id("Cn");
        Formula families = F.Id("families");
        Formula candidate = F.Id("T");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(formula, TypeUniverse()), Comma, RowBreak, Grp(),
            Typed(consequence, ConsequenceOperatorOf(formula)), Comma, Sp,
            Typed(families, SetOf(SetOf(formula))), Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, candidate, Comma, Sp,
            candidate, Sp, InMacro, Sp, families, Comma, Sp,
            IsFixedPoint(candidate, consequence),
            Close, Sp, Rightarrow, Sp, RowBreak, Grp(),
            IsFixedPoint(Call("sInf", families), consequence), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
