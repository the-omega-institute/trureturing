using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PriorityLattice;

internal sealed class IntervalForestBasicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/lillo2026prioritylattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Priority-forest interval structure and counting.", H("IntervalForestBasic"),
        Blocks(
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest"),
                DeclarationHandle.Create(Prefix + "IntervalForest"), H("IntervalForest"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("parent"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))), F.Sp, F.To, F.Sp, Kw("Option"), F.Sp, Parenthesized(F.Seq(Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))))), F.Sp, Parenthesized(F.Seq(Kw("increasing"), F.Sp, F.Colon, F.Sp, F.Forall, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, Kw("p"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.To, F.Sp, Kw("p"), F.Sp, F.Lt, F.Sp, Kw("v"))), F.Sp, Parenthesized(F.Seq(Kw("intervals"), F.Sp, F.Colon, F.Sp, F.Forall, F.Sp, Parenthesized(F.Seq(Kw("u"), F.Sp, Kw("v"), F.Sp, Kw("w"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("u"), F.Sp, F.Leq, F.Sp, Kw("v"), F.Sp, F.To, F.Sp, Kw("v"), F.Sp, F.Leq, F.Sp, Kw("w"), F.Sp, F.To, F.Sp, Kw("Relation.EqvGen"), F.Sp, Parenthesized(F.Seq(Kw("fun"), F.Sp, Parenthesized(F.Seq(Kw("a"), F.Sp, Kw("b"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Mapsto, F.Sp, Kw("parent"), F.Sp, Kw("b"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("a"))), F.Sp, Kw("u"), F.Sp, Kw("w"), F.Sp, F.To, F.Sp, Kw("Relation.EqvGen"), F.Sp, Parenthesized(F.Seq(Kw("fun"), F.Sp, Parenthesized(F.Seq(Kw("a"), F.Sp, Kw("b"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Mapsto, F.Sp, Kw("parent"), F.Sp, Kw("b"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("a"))), F.Sp, Kw("u"), F.Sp, Kw("v"))), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(Kw("IntervalForest.mk"), F.Sp, Kw("parent"), F.Sp, Kw("increasing"), F.Sp, Kw("intervals"))), F.Sp, F.Dot, F.Sp, Kw("parent"), F.Sp, F.Eq, F.Sp, Kw("parent")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Section 2.1, pp. 3–4: a priority forest (labeled with [n]₀ and with m edges) is a rooted forest (T₀, T₁, …, Tₙ₋ₘ) with all component trees increasing and ordered according to the root's labels, and where for all j<k, every label in Tⱼ is smaller than every label in Tₖ. Thus, the vertex set of each tree is an interval of integers. The parent-function fields use Fin (n + 1), a smaller parent for each non-root, and Relation.EqvGen for connected components."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-ext"),
                DeclarationHandle.Create(Prefix + "ext"), H("IntervalForest / ext"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, Kw("Q"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n")), F.CloseBrace), F.Sp, F.Comma, F.Sp, Kw("P.parent"), F.Sp, F.Eq, F.Sp, Kw("Q.parent"), F.Sp, F.To, F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, Kw("Q")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-edges"),
                DeclarationHandle.Create(Prefix + "edges"), H("IntervalForest / edges"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("edges"), F.Sp, Kw("P"), F.Sp, F.Eq, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("e"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))), F.Sp, F.Times, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))), F.Sp, F.Mid, F.Sp, Kw("P.parent"), F.Sp, Kw("e.2"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("e.1")), F.CloseBrace)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is {e | P.parent e.2 = some e.1}."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-edges-injective"),
                DeclarationHandle.Create(Prefix + "edges_injective"), H("IntervalForest / edges_injective"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("Function.Injective"), F.Sp, Parenthesized(F.Seq(Kw("fun"), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Mapsto, F.Sp, Kw("IntervalForestBasic.IntervalForest.edges"), F.Sp, Kw("P")))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-forestpartialorder"),
                DeclarationHandle.Create(Prefix + "forestPartialOrder"), H("IntervalForest / forestPartialOrder"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, Kw("Q"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("P"), F.Sp, F.Leq, F.Sp, Kw("Q"), F.Sp, F.Iff, F.Sp, Kw("IntervalForestBasic.IntervalForest.edges"), F.Sp, Kw("P"), F.Sp, F.Subseteq, F.Sp, Kw("IntervalForestBasic.IntervalForest.edges"), F.Sp, Kw("Q")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is PartialOrder.lift edges edges_injective."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-filtercount"),
                DeclarationHandle.Create(Prefix + "filterCount"), H("filterCount"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("filterCount"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Mid, F.Sp, F.Exists, F.Sp, Parenthesized(F.Seq(Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("m"), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.Land, F.Sp, Kw("Nonempty"), F.Sp, Parenthesized(F.Seq(Kw("Set.Ici"), F.Sp, Kw("x"), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForest"), F.Sp, Kw("m")))))), F.CloseBrace)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is Nat.card {x : (WithTop (IntervalForest n)) // ∃ m ≤ n, Nonempty (Set.Ici x ≃o (WithTop (IntervalForest m)))}."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-idealcount"),
                DeclarationHandle.Create(Prefix + "idealCount"), H("idealCount"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("idealCount"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Mid, F.Sp, F.Exists, F.Sp, Parenthesized(F.Seq(Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("m"), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.Land, F.Sp, Kw("Nonempty"), F.Sp, Parenthesized(F.Seq(Kw("Set.Iic"), F.Sp, Kw("x"), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForest"), F.Sp, Kw("m")))))), F.CloseBrace)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is Nat.card {x : (WithTop (IntervalForest n)) // ∃ m ≤ n, Nonempty (Set.Iic x ≃o (WithTop (IntervalForest m)))}."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-positiveidealcount"),
                DeclarationHandle.Create(Prefix + "positiveIdealCount"), H("positiveIdealCount"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, Kw("positiveIdealCount"), F.Sp, Kw("n"), F.Sp, F.Eq, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("x"), F.Sp, F.Colon, F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Mid, F.Sp, F.Exists, F.Sp, Parenthesized(F.Seq(Kw("m"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, F.Comma, F.Sp, F.D(1), F.Sp, F.Leq, F.Sp, Kw("m"), F.Sp, F.Land, F.Sp, Kw("m"), F.Sp, F.Leq, F.Sp, Kw("n"), F.Sp, F.Land, F.Sp, Kw("Nonempty"), F.Sp, Parenthesized(F.Seq(Kw("Set.Iic"), F.Sp, Kw("x"), F.Sp, new Formula.Subscript(F.Equiv, F.Id("o")), F.Sp, Kw("WithTop"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForest"), F.Sp, Kw("m")))))), F.CloseBrace)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is Nat.card {x : (WithTop (IntervalForest n)) // exists m, 1 <= m ∧ m <= n ∧ Nonempty (Set.Iic x ≃o (WithTop (IntervalForest m)))}."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-empty"),
                DeclarationHandle.Create(Prefix + "empty"), H("IntervalForest / empty"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(Kw("IntervalForest.empty"), F.Sp, Kw("n"))), F.Sp, F.Dot, F.Sp, Kw("parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("none")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is parent := fun _ => none increasing := by simp intervals := by intro u v w huv hvw h have hempty : forall a b : Fin (n+1), Relation.EqvGen (fun a _ => (none : Option (Fin (n+1))) = some a) a b -> a = b := by intro a b hab induction hab with | rel x y h => cases h | refl x => rfl | symm x y _ ih => exact ih.symm | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2 have huw : u = w := hempty u w h have huv' : u = v := le_antisymm huv (huw ▸ hvw) subst v exact Relation.EqvGen.refl _."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-parent-zero"),
                DeclarationHandle.Create(Prefix + "parent_zero"), H("IntervalForest / parent_zero"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("P.parent"), F.Sp, F.D(0), F.Sp, F.Eq, F.Sp, Kw("none")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-card-zero"),
                DeclarationHandle.Create(Prefix + "card_zero"), H("IntervalForest / card_zero"),
                StatementSource.FromAuthor(F.Disp(F.Seq(Kw("Nat.card"), F.Sp, Parenthesized(F.Seq(Kw("IntervalForestBasic.IntervalForest"), F.Sp, F.D(0))), F.Sp, F.Eq, F.Sp, F.D(1)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-intervalforest-no-skipped-root"),
                DeclarationHandle.Create(Prefix + "no_skipped_root"), H("IntervalForest / no_skipped_root"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N")))), F.CloseBrace), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("v"), F.Sp, Kw("p"), F.Sp, Kw("w"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1)))), F.CloseBrace), F.Sp, F.Comma, F.Sp, Kw("P.parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.To, F.Sp, Kw("p"), F.Sp, F.Lt, F.Sp, Kw("w"), F.Sp, F.To, F.Sp, Kw("w"), F.Sp, F.Leq, F.Sp, Kw("v"), F.Sp, F.To, F.Sp, Kw("P.parent"), F.Sp, Kw("w"), F.Sp, F.Neq, F.Sp, Kw("none")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The quantified statement holds for every parameter satisfying its displayed hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-forestoflocal"),
                DeclarationHandle.Create(Prefix + "forestOfLocal"), H("forestOfLocal"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("f"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))), F.Sp, F.To, F.Sp, Kw("Option"), F.Sp, Parenthesized(F.Seq(Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))))), F.Sp, Parenthesized(F.Seq(Kw("inc"), F.Sp, F.Colon, F.Sp, F.Forall, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, Kw("p"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("f"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.To, F.Sp, Kw("p"), F.Sp, F.Lt, F.Sp, Kw("v"))), F.Sp, Parenthesized(F.Seq(Kw("nskip"), F.Sp, F.Colon, F.Sp, F.Forall, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, Kw("p"), F.Sp, Kw("w"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("f"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Kw("p"), F.Sp, F.To, F.Sp, Kw("p"), F.Sp, F.Lt, F.Sp, Kw("w"), F.Sp, F.To, F.Sp, Kw("w"), F.Sp, F.Leq, F.Sp, Kw("v"), F.Sp, F.To, F.Sp, Kw("f"), F.Sp, Kw("w"), F.Sp, F.Neq, F.Sp, Kw("none"))), F.Sp, F.Comma, F.Sp, Parenthesized(F.Seq(Kw("forestOfLocal"), F.Sp, Kw("f"), F.Sp, Kw("inc"), F.Sp, Kw("nskip"))), F.Sp, F.Dot, F.Sp, Kw("parent"), F.Sp, F.Eq, F.Sp, Kw("f")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The literal parent function and increasing-parent proof, together with the no-skipped-root condition, construct the forest whose parent field is displayed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-istree"),
                DeclarationHandle.Create(Prefix + "IsTree"), H("IsTree"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForest"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("IsTree"), F.Sp, Kw("P"), F.Sp, F.Iff, F.Sp, F.Forall, F.Sp, Parenthesized(F.Seq(Kw("v"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Plus, F.Sp, F.D(1))))), F.Sp, F.Comma, F.Sp, Kw("P.parent"), F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, Kw("none"), F.Sp, F.To, F.Sp, Kw("v"), F.Sp, F.Eq, F.Sp, F.D(0)))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The defining expression is forall v, P.parent v = none -> v = 0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-treeequivcode"),
                DeclarationHandle.Create(Prefix + "treeEquivCode"), H("treeEquivCode"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, Kw("Nat"))), F.Sp, Parenthesized(F.Seq(Kw("T"), F.Sp, F.Colon, F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, Kw("IsTree"), F.Sp, Kw("P")), F.CloseBrace))), F.Sp, Parenthesized(F.Seq(Kw("i"), F.Sp, F.Colon, F.Sp, Kw("Fin"), F.Sp, Kw("n"))), F.Sp, F.Comma, F.Sp, Kw("Option.map"), F.Sp, Parenthesized(F.Seq(Kw("fun"), F.Sp, Kw("p"), F.Sp, F.Mapsto, F.Sp, Call("val", Kw("p")))), F.Sp, Parenthesized(F.Seq(Call("parent", Call("val", Kw("T"))), F.Sp, Kw("i.succ"))), F.Sp, F.Eq, F.Sp, Kw("some"), F.Sp, Parenthesized(F.Seq(Call("val", Parenthesized(F.Seq(Kw("treeEquivCode"), F.Sp, Kw("n"), F.Sp, Kw("T"), F.Sp, Kw("i"))))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The equivalence sends each vertex i + 1 to its parent label, which is at most i. The inverse attaches each non-root vertex to its prescribed parent."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prio-intervalforestbasic-increasing-tree-card"),
                DeclarationHandle.Create(Prefix + "increasing_tree_card"), H("increasing_tree_card"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, Parenthesized(F.Seq(Kw("n"), F.Sp, F.Colon, F.Sp, F.Seq(F.Mathbb, F.Grp(F.Id("N"))))), F.Sp, F.Comma, F.Sp, Kw("Nat.card"), F.Sp, F.Seq(F.OpenBrace, F.Seq(Kw("P"), F.Sp, F.Colon, F.Sp, Kw("IntervalForestBasic.IntervalForest"), F.Sp, Kw("n"), F.Sp, F.Mid, F.Sp, Kw("IntervalForestBasic.IsTree"), F.Sp, Kw("P")), F.CloseBrace), F.Sp, F.Eq, F.Sp, Kw("n.factorial")))),
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
