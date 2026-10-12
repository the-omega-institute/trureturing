using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PriorityLattice;

internal sealed class ForestCoversDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PriorityLattice/ForestCovers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/lillo2026prioritylattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Priority-forest interval structure and counting.", H("ForestCovers"),
        Blocks(
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-support"),
                DeclarationHandle.Create(Prefix + "support"), H("IntervalForest / support"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("support"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, Kw("Finset.univ.filter"), F.Sp, Parenthesized(F.Seq(Kw("fun"), F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Mapsto, F.Sp, Kw("P.parent"), F.Sp, Kw("v"), F.Sp, F.Neq, F.Sp, Kw("none")))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is by classical exact Finset.univ.filter (fun v => P.parent v ≠ none)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-mem-support"),
                DeclarationHandle.Create(Prefix + "mem_support"), H("IntervalForest / mem_support"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("v"), F.Sp, F.InMacro, F.Sp, Kw("ForestCovers.IntervalForest.support"), F.Sp, Kw("P"), F.Sp, F.Iff, F.Sp, Kw("P.parent"), F.Sp, Kw("v"), F.Sp, F.Neq, F.Sp, Kw("none")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-le-iff-parent"),
                DeclarationHandle.Create(Prefix + "le_iff_parent"), H("IntervalForest / le_iff_parent"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, Kw("Q"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("P"), F.Sp, F.Leq, F.Sp, Kw("Q"), F.Sp, F.Iff, F.Sp, F.Forall, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, Kw("p"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("P.parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.To, F.Sp, Kw("Q.parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-support-mono"),
                DeclarationHandle.Create(Prefix + "support_mono"), H("IntervalForest / support_mono"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, Kw("Q"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")), F.CloseBrace), F.Sp, F.Comma, F.Sp, Kw("P"), F.Sp, F.Leq, F.Sp, Kw("Q"), F.Sp, F.To, F.Sp, Kw("ForestCovers.IntervalForest.support"), F.Sp, Kw("P"), F.Sp, F.Subseteq, F.Sp, Kw("ForestCovers.IntervalForest.support"), F.Sp, Kw("Q")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-edgecount"),
                DeclarationHandle.Create(Prefix + "edgeCount"), H("IntervalForest / edgeCount"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, Parenthesized(F.Seq(Kw("support"), F.Sp, Kw("P"))), F.Sp, F.Dot, F.Sp, Kw("card")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is (support P).card."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-covby-iff-edgecount"),
                DeclarationHandle.Create(Prefix + "covBy_iff_edgeCount"), H("IntervalForest / covBy_iff_edgeCount"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, Kw("Q"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")), F.CloseBrace), F.Sp, F.Comma, F.Sp, Kw("P"), F.Sp, Kw("CovBy"), F.Sp, Kw("Q"), F.Sp, F.Iff, F.Sp, Kw("P"), F.Sp, F.Lt, F.Sp, Kw("Q"), F.Sp, F.Land, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("Q"), F.Sp, F.Eq, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Plus, F.Sp, F.D(1)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-edgecount-le"),
                DeclarationHandle.Create(Prefix + "edgeCount_le"), H("IntervalForest / edgeCount_le"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Leq, F.Sp, Kw("n")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-edgecount-eq-iff-tree"),
                DeclarationHandle.Create(Prefix + "edgeCount_eq_iff_tree"), H("IntervalForest / edgeCount_eq_iff_tree"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, Kw("n"), F.Sp, F.Iff, F.Sp, Kw("IntervalForestBasic.IsTree"), F.Sp, Kw("P")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-rank"),
                DeclarationHandle.Create(Prefix + "rank"), H("rank"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))))), F.Sp, F.Comma, F.Sp, Kw("rank"), F.Sp, Kw("x"), F.Sp, F.Eq, F.Sp, Kw("Option.elim"), F.Sp, Parenthesized(F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("Option"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))))), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))), F.Sp, Kw("ForestCovers.IntervalForest.edgeCount")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is (x : Option (IntervalForest n)).elim (n+1) IntervalForest.edgeCount."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-forestcovers-coatom-iff-tree"),
                DeclarationHandle.Create(Prefix + "coatom_iff_tree"), H("coatom_iff_tree"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("IsCoatom"), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))))), F.Sp, F.Iff, F.Sp, Kw("IntervalForestBasic.IsTree"), F.Sp, Kw("P")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-covby-rank"),
                DeclarationHandle.Create(Prefix + "covBy_rank"), H("covBy_rank"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, Kw("y"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")))), F.CloseBrace), F.Sp, F.Comma, F.Sp, Kw("x"), F.Sp, Kw("CovBy"), F.Sp, Kw("y"), F.Sp, F.To, F.Sp, Kw("ForestCovers.rank"), F.Sp, Kw("y"), F.Sp, F.Eq, F.Sp, Kw("ForestCovers.rank"), F.Sp, Kw("x"), F.Sp, F.Plus, F.Sp, F.D(1)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-atom-card-orderiso"),
                DeclarationHandle.Create(Prefix + "atom_card_orderIso"), H("atom_card_orderIso"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("A"), F.Sp, F.Colon, F.Sp, Kw("Type")), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("B"), F.Sp, F.Colon, F.Sp, Kw("Type")), F.CloseBrace), F.Sp, F.Seq(F.OpenBracket, F.Seq(Kw("PartialOrder"), F.Sp, Kw("A")), F.CloseBracket), F.Sp, F.Seq(F.OpenBracket, F.Seq(Kw("PartialOrder"), F.Sp, Kw("B")), F.CloseBracket), F.Sp, F.Seq(F.OpenBracket, F.Seq(Kw("OrderBot"), F.Sp, Kw("A")), F.CloseBracket), F.Sp, F.Seq(F.OpenBracket, F.Seq(Kw("OrderBot"), F.Sp, Kw("B")), F.CloseBracket), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(Kw("A"), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("B"))), F.Sp, F.To, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("a"), F.Sp, F.Colon, F.Sp, Kw("A"), F.Sp, F.Mid, F.Sp, Kw("IsAtom"), F.Sp, Kw("a")), F.CloseBrace), F.Sp, F.Eq, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("b"), F.Sp, F.Colon, F.Sp, Kw("B"), F.Sp, F.Mid, F.Sp, Kw("IsAtom"), F.Sp, Kw("b")), F.CloseBrace)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-eq-of-same-support-below"),
                DeclarationHandle.Create(Prefix + "eq_of_same_support_below"), H("IntervalForest / eq_of_same_support_below"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, Kw("Q"), F.Sp, Kw("R"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")), F.CloseBrace), F.Sp, F.Comma, F.Sp, Kw("Q"), F.Sp, F.Leq, F.Sp, Kw("P"), F.Sp, F.To, F.Sp, Kw("R"), F.Sp, F.Leq, F.Sp, Kw("P"), F.Sp, F.To, F.Sp, Kw("ForestCovers.IntervalForest.support"), F.Sp, Kw("Q"), F.Sp, F.Eq, F.Sp, Kw("ForestCovers.IntervalForest.support"), F.Sp, Kw("R"), F.Sp, F.To, F.Sp, Kw("Q"), F.Sp, F.Eq, F.Sp, Kw("R")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-lower-covers-card-le"),
                DeclarationHandle.Create(Prefix + "lower_covers_card_le"), H("IntervalForest / lower_covers_card_le"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("Q"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, Kw("Q"), F.Sp, Kw("CovBy"), F.Sp, Kw("P")), F.CloseBrace), F.Sp, F.Leq, F.Sp, Kw("ForestCovers.IntervalForest.edgeCount"), F.Sp, Kw("P")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-ideal-iso-rank"),
                DeclarationHandle.Create(Prefix + "ideal_iso_rank"), H("ideal_iso_rank"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, Kw("m"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")))), F.CloseBrace), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(new Formula.Apply(Kw("CoeSort.coe"), [F.Seq(Kw("Set.Iic"), F.Sp, Kw("x"))]), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("m"))))), F.Sp, F.To, F.Sp, Kw("ForestCovers.rank"), F.Sp, Kw("x"), F.Sp, F.Eq, F.Sp, Kw("m"), F.Sp, F.Plus, F.Sp, F.D(1)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-filter-iso-rank"),
                DeclarationHandle.Create(Prefix + "filter_iso_rank"), H("filter_iso_rank"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, Kw("m"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")))), F.CloseBrace), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(new Formula.Apply(Kw("CoeSort.coe"), [F.Seq(Kw("Set.Ici"), F.Sp, Kw("x"))]), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("m"))))), F.Sp, F.To, F.Sp, Kw("m"), F.Sp, F.Plus, F.Sp, F.D(1), F.Sp, F.Eq, F.Sp, Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1), F.Sp, F.Minus, F.Sp, Kw("ForestCovers.rank"), F.Sp, Kw("x")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-top-filter-not-iso"),
                DeclarationHandle.Create(Prefix + "top_filter_not_iso"), H("top_filter_not_iso"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, F.Neg, F.Sp, Kw("Nonempty"), F.Sp, Parenthesized(F.Seq(Kw("Set.Ici"), F.Sp, Parenthesized(F.Seq(Kw("Top.top"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))))), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("m")))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-forest-ideal-index-le-two"),
                DeclarationHandle.Create(Prefix + "forest_ideal_index_le_two"), H("forest_ideal_index_le_two"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(Kw("Set.Iic"), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))))), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("m"))))), F.Sp, F.To, F.Sp, Kw("m"), F.Sp, F.Leq, F.Sp, F.D(2)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-forestcovers-intervalforest-cover-adjacent-roots"),
                DeclarationHandle.Create(Prefix + "cover_adjacent_roots"), H("IntervalForest / cover_adjacent_roots"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, Kw("Q"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")), F.CloseBrace), F.Sp, F.Comma, F.Sp, Kw("P"), F.Sp, Kw("CovBy"), F.Sp, Kw("Q"), F.Sp, F.To, F.Sp, F.Exists, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, Kw("p"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("P.parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("none"), F.Sp, F.Land, F.Sp, Kw("Q.parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.Land, F.Sp, Kw("p"), F.Sp, F.Lt, F.Sp, Kw("v"), F.Sp, F.Land, F.Sp, Parenthesized(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("w"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("p"), F.Sp, F.Lt, F.Sp, Kw("w"), F.Sp, F.To, F.Sp, Kw("w"), F.Sp, F.Lt, F.Sp, Kw("v"), F.Sp, F.To, F.Sp, Kw("P.parent"), F.Sp, Kw("w"), F.Sp, F.Neq, F.Sp, Kw("none"))), F.Sp, F.Land, F.Sp, Parenthesized(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("w"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("w"), F.Sp, F.Neq, F.Sp, Kw("v"), F.Sp, F.To, F.Sp, Kw("Q.parent"), F.Sp, Kw("w"), F.Sp, F.Eq, F.Sp, Kw("P.parent"), F.Sp, Kw("w")))))),
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
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
}
