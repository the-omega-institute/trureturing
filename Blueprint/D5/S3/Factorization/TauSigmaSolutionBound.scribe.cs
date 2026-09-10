using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class TauSigmaSolutionBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/TauSigmaSolutionBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bound on positive tau-sigma fixed points, with finite classification still open.",
        H("A336687 Solution Bound"),
        Blocks(
            Paragraph(Text("This module does not prove the A336687 conjecture. It proves "
                + "only that every positive solution is below 3^13. The finite exhaustive "
                + "classification needed to obtain the three-solution theorem remains "
                + "an explicit unproved hypothesis.")),
            Describe.Lean(
                DescribeId.Create("tau-sigma-solution-bound"),
                DeclarationHandle.Create(Prefix + "tau_sigma_solution_lt"),
                H("Every positive solution is below 3^13"),
                StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Arith/ianakiev2020a336687")),
                Blocks(Paragraph(Text("Apply each uniform fourth-power estimate twice. "
                    + "Multiplying the resulting sixteenth-power inequalities gives "
                    + "m^16 <= 3^77*m^10. Positivity permits cancellation, so "
                    + "m^6 <= 3^77 < (3^13)^6, yielding m < 1594323."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditional-three-solutions"),
                DeclarationHandle.Create(Prefix + "tau_sigma_product_eq_self_iff_of_finite"),
                H("Conditional three-solution classification"),
                StatementSource.FromAuthor(ConditionalFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Arith/ianakiev2020a336687")),
                Blocks(Paragraph(Text("The hypothesis hfinite asserts the complete "
                    + "equivalence on 1 <= n < 3^13. It is not established by this module. "
                    + "Under that hypothesis the proved bound extends the equivalence to "
                    + "all positive m. No unconditional resolution claim is made."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, Formula n) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, n, Close);

    private static Formula Equality(Formula n) => new Formula.Relation(
        new Formula.Binary(Call("tau", Call("sigma", n)), FormulaBinaryOperator.Multiply,
            Call("sigma", Call("tau", n))), FormulaRelationOperator.Equal, n);

    private static Formula Positive(Formula n) =>
        new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);

    private static Formula Below(Formula n) => new Formula.Relation(
        n, FormulaRelationOperator.LessThan, new Formula.Power(D(3), D(1, 3)));

    private static Formula Solutions(Formula n) => new Formula.Logic(
        new Formula.Relation(n, FormulaRelationOperator.Equal, D(1)), FormulaLogicOperator.Or,
        new Formula.Logic(new Formula.Relation(n, FormulaRelationOperator.Equal, D(4, 6, 8)),
            FormulaLogicOperator.Or, new Formula.Relation(n, FormulaRelationOperator.Equal,
                D(3, 2, 4, 0))));

    private static Formula Equivalence(Formula n) =>
        new Formula.Logic(Equality(n), FormulaLogicOperator.Iff, Solutions(n));

    private static Formula Universal(string name, Formula body) => Seq(
        Forall, Sp, F.Id(name), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, body);

    private static Formula BoundFormula()
    {
        var m = F.Id("m");
        return Disp(Universal("m", Seq(Positive(m), Sp, Implies, Sp,
            Equality(m), Sp, Implies, Sp, Below(m))));
    }

    private static Formula ConditionalFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        return Disp(Seq(Open, Universal("n", Seq(Positive(n), Sp, Implies, Sp,
                Below(n), Sp, Implies, Sp, Equivalence(n))), Close, Sp, Implies, Sp,
            Universal("m", Seq(Positive(m), Sp, Implies, Sp, Equivalence(m)))));
    }
}
