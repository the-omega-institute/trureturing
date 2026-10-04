using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class SelfCalibratingRulingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings.";
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive eigenvector rulings obstruct three-read recovery except at nontrivial shear second endpoints.",
        H("Positive Rulings and Actual Second Queries"),
        Blocks(
            Paragraph(Text(
                "R is a real 2 by 2 matrix with all four entries strictly positive and "
                + "R11 R22=R12 R21. At cumulative A the exact read is trace(AR).")),
            Paragraph(Text(
                "A query is a pair (previous literal word,new finite segment). Histories "
                + "record that query and its real response. A policy is an arbitrary function "
                + "from histories to either a next query or an output relation with an unread "
                + "finite tail. It first queries the empty word. OriginalValid requires every "
                + "source to terminate under native execution with at most three reads, "
                + "chronological prefix extension, and output equal to the initial R. "
                + "Action cost is the sum of segment lengths plus the terminal tail length.")),
            Describe.Lean(DescribeId.Create("self-calibrating-positive-ruling-collision"),
                DeclarationHandle.Create(Prefix + "positive_ruling_collision"),
                H("A collision for every third linear read"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, F.Id("B"), Comma, F.Id("c"), Comma,
                    F.Id("l"), Comma, F.Id("lambda"), Sp,
                    Call("PositiveEigenvectors", F.Id("A"), F.Id("c"), F.Id("l"), F.Id("lambda")),
                    Sp, Implies, Sp, Call("RulingCollision", F.Id("A"), F.Id("B"), F.Id("c"), F.Id("l"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive column c and row l satisfy Ac=lambda c "
                    + "and lA=lambda l. For every real B there are two distinct positive "
                    + "rank-one sources with the same initial trace lc, the same A read "
                    + "lambda lc, and the same B read. Perturbing the row and column along "
                    + "their annihilating directions preserves the first two reads. Small "
                    + "parameters retain positivity; matching the third slopes gives a "
                    + "collision, including when either slope is zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("self-calibrating-second-query-shear"),
                DeclarationHandle.Create(Prefix + "second_query_shear"),
                H("Global correctness forces the actual second shear"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("P"), Comma, F.Id("x"), Sp,
                    Call("OriginalValid", F.Id("P")), Sp, Land, Sp, F.Id("x"), Sp, Gt, D(0),
                    Sp, Implies, Sp, Exists, Sp, F.Id("w"), Comma, F.Id("k"), Comma, Sp,
                    Call("ActualSecondShear", F.Id("P"), F.Id("x"), F.Id("w"), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every x>0, P selects a second query with empty "
                    + "previous word and a finite literal word w. For some natural k>0, "
                    + "E(w) has rows (1,k),(0,1) or (1,0),(k,1). Stopping after the first "
                    + "read fails on distinct sources of that trace. Two positive offdiagonals "
                    + "supply positive left and right eigenvectors, whose rulings defeat "
                    + "every history-selected third query. Integral nonnegative entries and "
                    + "determinant of absolute value one leave the shear forms. Identity "
                    + "has the same ruling obstruction and is excluded. No continuity of "
                    + "P, finite candidate set, or uniform action budget is required. "
                    + "Every source also has the explicit positive factorization "
                    + "c=(R11,R21), l=(1,R12/R11). For every word its relation read "
                    + "is l(E(w)c). The same l is retained throughout that source's run; "
                    + "different compatible sources may have different positive rows."))),
                DescribeRole.Theorem))));
}
