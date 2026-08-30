using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BilateralLiftClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "The bilateral Fibonacci lift is the unique two-line golden eigenlift up to independent component scales.",
            H("Bilateral Fibonacci Lift Classification"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("bilateral-lift-classification"),
                    DeclarationHandle.Create("D5/S1/Recurrence/BilateralLiftClassification.bilateral_lift_classification"),
                    H("The bilateral lift is two-dimensional and componentwise unique"),
                    StatementSource.FromAuthor(TheoremFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The source row phi = (1+sqrt(5))/2 is a definition (not a conjunct).")),
                        Paragraph(Text(
                            "The public statement retains the solution-space dimension, golden conjugacy identity, "
                                + "shift eigenlaws, nonzero Binet coefficients, least invariant carrier, its dimension, "
                                + "and two independently premised unique component-scalar classifications."))),
                    DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Member(Formula value, Formula carrier) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, carrier);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula sequence = Call("Seq", real);
        Formula phi = Varphi;
        Formula psi = Psi;
        Formula expanding = Seq(F.Id("e"), Underscore, Grp(phi));
        Formula contracting = Seq(F.Id("e"), Underscore, Grp(psi));
        Formula fibonacci = F.Id("F");
        Formula shift = F.Id("S");
        Formula k = F.Id("k");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula w = F.Id("W");
        Formula expandingScale = F.Id("a");
        Formula contractingScale = F.Id("b");
        Formula solutionSpace = Call("Sol", F.Id("fibRec"));
        Formula carrier = Call("span", real, expanding, contracting);
        Formula sqrtFive = Seq(Sqrt, Grp(D(5)));
        Formula coefficient = Call("inv", sqrtFive);
        Formula expandingEigenlaw = Seq(
            Apply(shift, u), Sp, Eq, Sp, phi, Sp, Cdot, Sp, u);
        Formula contractingEigenlaw = Seq(
            Apply(shift, v), Sp, Eq, Sp, psi, Sp, Cdot, Sp, v);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Call("finrank", real, solutionSpace), Sp, Eq, Sp, D(2), Sp, Land,
            RowBreak, Grp(),
            solutionSpace, Sp, Eq, Sp, carrier, Sp, Land,
            RowBreak, Grp(),
            psi, Sp, Eq, Sp, Minus, Call("inv", phi), Sp, Land,
            RowBreak, Grp(),
            Apply(shift, expanding), Sp, Eq, Sp, phi, Sp, Cdot, Sp, expanding,
            Sp, Land, Sp,
            Apply(shift, contracting), Sp, Eq, Sp, psi, Sp, Cdot, Sp, contracting,
            Sp, Land,
            RowBreak, Grp(),
            coefficient, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Minus, coefficient, Sp, Neq, Sp, D(0), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, k, Colon, Sp, natural, Comma, Sp,
            Apply(fibonacci, k), Sp, Eq, Sp,
            Frac,
            Grp(Apply(expanding, k), Sp, Minus, Sp, Apply(contracting, k)),
            Grp(sqrtFive), Close, Sp, Land,
            RowBreak, Grp(),
            Member(fibonacci, carrier), Sp, Land, Sp,
            Open, Forall, Sp, u, Colon, Sp, sequence, Comma, Sp,
            Member(u, carrier), Sp, Rightarrow, Sp,
            Member(Apply(shift, u), carrier), Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, w, Colon, Sp, Call("Submodule", real, sequence), Comma, Sp,
            Member(fibonacci, w), Sp, Land, Sp,
            Open, Forall, Sp, u, Colon, Sp, sequence, Comma, Sp,
            Member(u, w), Sp, Rightarrow, Sp,
            Member(Apply(shift, u), w), Close, Sp,
            Rightarrow, Sp, carrier, Sp, Subseteq, Sp, w, Close, Sp, Land,
            RowBreak, Grp(),
            Call("finrank", real, carrier), Sp, Eq, Sp, D(2), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, u, Colon, Sp, sequence, Comma, Sp,
            expandingEigenlaw, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, expandingScale, Colon, Sp, real, Comma, Sp,
            u, Sp, Eq, Sp, expandingScale, Sp, Cdot, Sp, expanding,
            Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, v, Colon, Sp, sequence, Comma, Sp,
            contractingEigenlaw, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, contractingScale, Colon, Sp, real, Comma, Sp,
            v, Sp, Eq, Sp, contractingScale, Sp, Cdot, Sp, contracting,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
