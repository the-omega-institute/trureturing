using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PriorityLattice;

internal sealed class LowRankForestsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PriorityLattice/LowRankForests.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/lillo2026prioritylattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Priority-forest interval structure and counting.", H("LowRankForests"),
        Blocks(
            Describe.Lean(DescribeId.Create("prio-lowrankforests-onelongat"),
                DeclarationHandle.Create(Prefix + "OneLongAt"), H("OneLongAt"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForest"), F.Sp, Kw("n"))), F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("OneLongAt"), F.Sp, Kw("P"), F.Sp, Kw("v"), F.Sp, F.Iff, F.Sp, Parenthesized(F.Seq(F.Exists, F.Sp, Parenthesized(F.Seq(Kw("p"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("P.parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.Land, F.Sp, Call("val", Kw("p")), F.Sp, F.Plus, F.Sp, F.D(2), F.Sp, F.Eq, F.Sp, Call("val", Kw("v")))), F.Sp, F.Land, F.Sp, Parenthesized(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("w"), F.Sp, Kw("p"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("w"), F.Sp, F.Neq, F.Sp, Kw("v"), F.Sp, F.To, F.Sp, Kw("P.parent"), F.Sp, Kw("w"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.To, F.Sp, Call("val", Kw("p")), F.Sp, F.Plus, F.Sp, F.D(1), F.Sp, F.Eq, F.Sp, Call("val", Kw("w"))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("OneLongAt means that v has a parent two labels below it, and every other non-root has a parent one label below it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-onelong"),
                DeclarationHandle.Create(Prefix + "OneLong"), H("OneLong"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("OneLong"), F.Sp, Kw("P"), F.Sp, F.Iff, F.Sp, F.Exists, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("OneLongAt"), F.Sp, Kw("P"), F.Sp, Kw("v")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is ∃ v, OneLongAt P v."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-codeonestep"),
                DeclarationHandle.Create(Prefix + "CodeOneStep"), H("CodeOneStep"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("k"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("t"), F.Sp, F.Colon, F.Sp, Parenthesized(F.Seq(Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Kw("k"))), F.Sp, F.To, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Call("val", Kw("v")), F.Sp, F.Plus, F.Sp, F.D(1))))))), F.Sp, F.Comma, F.Sp, Kw("CodeOneStep"), F.Sp, Kw("t"), F.Sp, F.Iff, F.Sp, F.Exists, F.Sp, Kw("i"), F.Sp, Kw("j"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Kw("k"), F.Sp, F.Comma, F.Sp, Call("val", Kw("i")), F.Sp, F.Plus, F.Sp, F.D(1), F.Sp, F.Eq, F.Sp, Call("val", Kw("j")), F.Sp, F.Land, F.Sp, Call("val", Parenthesized(F.Seq(Kw("t"), F.Sp, Kw("j")))), F.Sp, F.Eq, F.Sp, Call("val", Kw("i")), F.Sp, F.Land, F.Sp, Parenthesized(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("z"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Kw("k"))), F.Sp, F.Comma, F.Sp, Kw("z"), F.Sp, F.Neq, F.Sp, Kw("j"), F.Sp, F.To, F.Sp, Call("val", Parenthesized(F.Seq(Kw("t"), F.Sp, Kw("z")))), F.Sp, F.Eq, F.Sp, Call("val", Kw("z"))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("CodeOneStep has one pair of adjacent indices i and j with val(t j) = val(i); every other index z has val(t z) = val(z)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-intervalforest-one-long-iff-code-one-step"),
                DeclarationHandle.Create(Prefix + "one_long_iff_code_one_step"), H("IntervalForest / one_long_iff_code_one_step"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, Kw("k"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, Parenthesized(F.Seq(Kw("h"), F.Sp, F.Colon, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, Kw("k"))), F.Sp, F.Comma, F.Sp, Kw("LowRankForests.OneLong"), F.Sp, Kw("P"), F.Sp, F.Iff, F.Sp, Kw("LowRankForests.CodeOneStep"), F.Sp, Parenthesized(F.Seq(Kw("IdealCompression.IntervalForest.compressCode"), F.Sp, Kw("P"), F.Sp, Kw("h")))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-smallidealcodes-onestep-two-iff"),
                DeclarationHandle.Create(Prefix + "oneStep_two_iff"), H("SmallIdealCodes / oneStep_two_iff"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("t"), F.Sp, F.Colon, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, F.D(2))), F.Sp, F.To, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Call("val", Kw("v")), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("LowRankForests.CodeOneStep"), F.Sp, Kw("t"), F.Sp, F.Iff, F.Sp, Kw("t"), F.Sp, F.Eq, F.Sp, Kw("IdealCompression.SmallIdealCodes.t20")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-smallidealcodes-onestep-three-iff"),
                DeclarationHandle.Create(Prefix + "oneStep_three_iff"), H("SmallIdealCodes / oneStep_three_iff"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("t"), F.Sp, F.Colon, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, F.D(3))), F.Sp, F.To, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Call("val", Kw("v")), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("LowRankForests.CodeOneStep"), F.Sp, Kw("t"), F.Sp, F.Iff, F.Sp, Kw("t"), F.Sp, F.Eq, F.Sp, Kw("IdealCompression.SmallIdealCodes.t3"), F.Sp, F.D(0), F.Sp, F.D(2), F.Sp, F.Lor, F.Sp, Kw("t"), F.Sp, F.Eq, F.Sp, Kw("IdealCompression.SmallIdealCodes.t3"), F.Sp, F.D(1), F.Sp, F.D(1)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-long-two-card"),
                DeclarationHandle.Create(Prefix + "long_two_card"), H("long_two_card"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N"))))), F.Sp, F.Comma, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, F.D(2), F.Sp, F.Land, F.Sp, Kw("LowRankForests.OneLong"), F.Sp, Kw("P")), F.CloseBrace), F.Sp, F.Eq, F.Sp, Kw("n"), F.Sp, F.Minus, F.Sp, F.D(1)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-long-three-card"),
                DeclarationHandle.Create(Prefix + "long_three_card"), H("long_three_card"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N"))))), F.Sp, F.Comma, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, F.D(3), F.Sp, F.Land, F.Sp, Kw("LowRankForests.OneLong"), F.Sp, Kw("P")), F.CloseBrace), F.Sp, F.Eq, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Minus, F.Sp, F.D(1))), F.Sp, F.Cdot, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Minus, F.Sp, F.D(2)))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-lowrankforests-single-edges-card"),
                DeclarationHandle.Create(Prefix + "single_edges_card"), H("single_edges_card"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N"))))), F.Sp, F.Comma, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, F.D(1)), F.CloseBrace), F.Sp, F.Eq, F.Sp, Kw("n")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem)), []));

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
    private static Formula Call(string name, Formula operand) =>
        F.Seq(Kw(name), Parenthesized(operand));
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
}
