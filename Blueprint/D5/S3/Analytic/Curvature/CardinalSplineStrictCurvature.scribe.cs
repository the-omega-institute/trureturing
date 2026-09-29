using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Curvature;

internal sealed class CardinalSplineStrictCurvatureDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Curvature/CardinalSplineStrictCurvature.cardinalSpline_strict_curvature";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized cardinal spline has strictly negative curvature on its shifted closed "
            + "central core in every order at least five.",
        H("Strict Curvature of Normalized Cardinal Splines"),
        Blocks(
            Paragraph(Text(
                "The proof is an induction on the spline order built entirely on the single "
                    + "finite positive-part representation and the recurrences recorded in the "
                    + "preceding module. Its private invariant carries five simultaneous facts: "
                    + "support outside [0,m], reflection D_m(m-x)=-D_m(x), global Q_m(u)>=0 for "
                    + "every u>=0, strict positivity Q_m(1/2)>0, and strict decrease of D_m on "
                    + "[s_m,m-s_m]. These are proof-local facts, not additional public declarations.")),
            Describe.Lean(
                DescribeId.Create("strict-cardinal-spline-curvature"),
                DeclarationHandle.Create(Declaration),
                H("Strict negativity on the closed core"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural order m>=5 and every x in the closed interval "
                            + "[s_m,m-s_m], the curvature specialization C_m(x) is strictly "
                            + "negative. The closed endpoints are part of the assertion.")),
                    Paragraph(Text(
                        "At order four, direct piecewise evaluation establishes the support and "
                            + "reflection laws, global nonnegativity of Q_4, Q_4(1/2)=1/18, and "
                            + "strict decrease of D_4 on its closed core. The associated C_4 is "
                            + "negative only in the core interior and is zero at 4/3 and 8/3; "
                            + "therefore the public strict-curvature theorem deliberately begins "
                            + "at order five.")),
                    Paragraph(Text(
                        "For the induction step, the centered integral recurrence preserves "
                            + "global Q nonnegativity. When the centered window crosses zero, "
                            + "oddness cancels the symmetric part and leaves an integral over a "
                            + "nonnegative interval. Continuity plus the positive value at 1/2 "
                            + "makes the next half-offset integral strictly positive. The left "
                            + "half of the next core is split into t=1/2, 1/2<t<1, and "
                            + "1<=t<=7/6. The half-offset Q inequality and strict decrease of D "
                            + "give negativity in these branches; reflection gives the right "
                            + "half. Differentiating D then propagates strict decrease and closes "
                            + "the invariant."))),
                DescribeRole.Theorem))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m");
        Formula x = F.Id("x");
        Formula lower = Call("s", m);
        Formula upper = Seq(m, Sp, Minus, Sp, lower);
        Formula inCore = Seq(x, Sp, InMacro, Sp, OpenBracket, lower, Comma, Sp, upper, CloseBracket);
        Formula negative = new Formula.Relation(
            Call("C", m, x), FormulaRelationOperator.LessThan, D(0));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, m, Sp, InMacro, Sp, Naturals, Comma, Sp,
                D(5), Sp, Leq, Sp, m, Comma),
            Seq(Forall, Sp, x, Sp, InMacro, Sp, Reals, Comma, Sp,
                inCore, Sp, Implies, Sp, negative, Dot),
        ]));
    }
}
