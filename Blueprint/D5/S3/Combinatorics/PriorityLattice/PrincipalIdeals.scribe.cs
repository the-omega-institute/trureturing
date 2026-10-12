using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PriorityLattice;

internal sealed class PrincipalIdealsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PriorityLattice/PrincipalIdeals.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/lillo2026prioritylattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Priority-forest interval structure and counting.", H("PrincipalIdeals"),
        Blocks(
            Describe.Lean(DescribeId.Create("prio-principalideals-forest-ideal-shape-iff"),
                DeclarationHandle.Create(Prefix + "forest_ideal_shape_iff"), H("forest_ideal_shape_iff"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(F.Exists, F.Sp, Parenthesized(F.Seq(Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("m"), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.Land, F.Sp, Kw("Nonempty"), F.Sp, Parenthesized(F.Seq(Kw("Set.Iic"), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))))), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("m"))))))), F.Sp, F.Iff, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, F.D(1), F.Sp, F.Lor, F.Sp, Parenthesized(F.Seq(Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, F.D(2), F.Sp, F.Land, F.Sp, Kw("LowRankForests.OneLong"), F.Sp, Kw("P"))), F.Sp, F.Lor, F.Sp, Parenthesized(F.Seq(Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, F.D(3), F.Sp, F.Land, F.Sp, Kw("LowRankForests.OneLong"), F.Sp, Kw("P")))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-principalideals-gamma-formula"),
                DeclarationHandle.Create(Prefix + "gamma_formula"), H("gamma_formula"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N"))))), F.Sp, F.Comma, F.Sp, F.D(1), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.To, F.Sp, Kw("IntervalForestBasic.idealCount"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, new Formula.Power(Kw("n"), F.D(2)), F.Sp, F.Minus, F.Sp, Kw("n"), F.Sp, F.Plus, F.Sp, F.D(2)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-principalideals-gammapos-formula"),
                DeclarationHandle.Create(Prefix + "gammaPos_formula"), H("gammaPos_formula"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N"))))), F.Sp, F.Comma, F.Sp, F.D(1), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.To, F.Sp, Kw("IntervalForestBasic.positiveIdealCount"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, new Formula.Power(Kw("n"), F.D(2)), F.Sp, F.Plus, F.Sp, F.D(2), F.Sp, F.Minus, F.Sp, F.D(2), F.Sp, F.Cdot, F.Sp, Kw("n")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-principalideals-gamma"),
                DeclarationHandle.Create(Prefix + "gamma"), H("gamma"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("gamma"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("Pi"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, F.Exists, F.Sp, Parenthesized(F.Seq(Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("m"), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.Land, F.Sp, Kw("Nonempty"), F.Sp, Parenthesized(F.Seq(Kw("Set.Iic"), F.Sp, Kw("x"), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("Pi"), F.Sp, Kw("m")))), F.CloseBrace)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is Nat.card {x : Pi n // ∃ m ≤ n, Nonempty (Set.Iic x ≃o Pi m)}."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-principalideals-gammapos"),
                DeclarationHandle.Create(Prefix + "gammaPos"), H("gammaPos"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("gammaPos"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("Pi"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, F.Exists, F.Sp, Parenthesized(F.Seq(Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, F.D(1), F.Sp, F.Leq, F.Sp, Kw("m"), F.Sp, F.Land, F.Sp, Kw("m"), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.Land, F.Sp, Kw("Nonempty"), F.Sp, Parenthesized(F.Seq(Kw("Set.Iic"), F.Sp, Kw("x"), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("Pi"), F.Sp, Kw("m")))), F.CloseBrace)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is Nat.card {x : Pi n // ∃ m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic x ≃o Pi m)}."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-principalideals-claimgamma"),
                DeclarationHandle.Create(Prefix + "claimGamma"), H("claimGamma"),
                StatementSource.FromAuthor(F.Disp(F.Seq(Kw("claimGamma"), F.Sp, F.Iff, F.Sp, F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, F.D(1), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.To, F.Sp, Kw("gamma"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, new Formula.Power(Kw("n"), F.D(2)), F.Sp, F.Minus, F.Sp, Kw("n"), F.Sp, F.Plus, F.Sp, F.D(2), F.Sp, F.Land, F.Sp, Kw("gammaPos"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, new Formula.Power(Kw("n"), F.D(2)), F.Sp, F.Plus, F.Sp, F.D(2), F.Sp, F.Minus, F.Sp, F.D(2), F.Sp, F.Cdot, F.Sp, Kw("n")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Section 6, item 3, p. 24: How many principal ideals of Π(n) are isomorphic to Π(m), for some 1≤ m≤ n? Let γₙ denote the number of principal ideals of Π(n) that are isomorphic to Π(m) with m ≤ n. The sequence (γₙ)ₙ≥₁ begins as 2, 4, 8, 14, 22 ,32, 44, … This sequence seems to be https://oeis.org/A014206, which is given by the formula γₙ = n² + n + 2. The data give n² − n + 2, with m = 0 allowed. The positive-parameter reading gives n² + 2 − 2n. Both counts include the greatest element's ideal; natural subtraction is taken in the displayed order. These are the counting conventions of Lillo and Rosas; the count formulas resolve their final-section questions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-principalideals-result"),
                DeclarationHandle.Create(Prefix + "result"), H("result"),
                StatementSource.FromAuthor(F.Disp(Kw("claimGamma"))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lillo-rosas-2026-priority-lattice-principal-ideals"),
                    ResolutionKind.Proved))), []));

    private static Formula Kw(string name)
    {
        var parts = name.Split('.');
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(F.Dot);
            var words = part.Split('_');
            Formula value = Word(words[0]);
            foreach (var word in words.Skip(1)) value = new Formula.Subscript(value, Word(word));
            tokens.Add(value);
        }
        return F.Seq(F.Operatorname, F.Grp(F.Seq([.. tokens])));
    }
    private static Formula Word(string word) => word switch
    {
        "0" => F.D(0), "1" => F.D(1), "2" => F.D(2), "3" => F.D(3),
        "4" => F.D(4), "5" => F.D(5), "6" => F.D(6), "7" => F.D(7),
        "8" => F.D(8), "9" => F.D(9), "" => new Formula.Placeholder(), _ => F.Id(word)
    };
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
}
