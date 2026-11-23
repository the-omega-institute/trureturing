using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.VertexDeletion;

internal sealed class BalancedCutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced cuts uniquely maximize pair and largest-component damage.",
        H("Balanced cuts optimize pairwise and largest-component damage"),
        Blocks(
            Describe.Lean(DescribeId.Create("uniform-prefix-le-q"), DeclarationHandle.Create(Prefix + "uniform_prefix_le_q"),
                H("Uniform prefix le q"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The size of the intact prefix fits inside one balanced part."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-prefix-lt-q"), DeclarationHandle.Create(Prefix + "uniform_prefix_lt_q"),
                H("Uniform prefix lt q"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma, Sp, D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, FormulaDsl.Lt, Sp, Id("q")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Strict inequality leaves room for the positive first tail run."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-balanced-deletion"), DeclarationHandle.Create(Prefix + "uniformBalancedDeletion"),
                H("Uniform balanced deletion"), StatementSource.FromAuthor(Disp(Seq(Word("uniformBalancedDeletion"), Sp, Colon, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Delete the b prescribed tail positions, each separated from the next by q survivors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-balanced-deletion-card"), DeclarationHandle.Create(Prefix + "uniform_balanced_deletion_card"),
                H("Uniform balanced deletion card"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hq"), Sp, Colon, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Close, Comma, Sp, Open, Word("uniformBalancedDeletion"), Sp, Word("hq"), Close, Dot, Word("card"), Sp, Eq, Sp, Id("b")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The ordered tail positions are distinct, so the prescribed cut has exactly b deletions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-balanced-deletion-profile"), DeclarationHandle.Create(Prefix + "uniform_balanced_deletion_profile"),
                H("Uniform balanced deletion profile"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Open, Word("hb"), Sp, Colon, Sp, D(2), Sp, Leq, Sp, Id("b"), Close, Comma),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Word("hq"), Sp, Colon, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Close, Comma),
                Seq(Word("have"), Sp, Id("D"), Sp, Colon, Sp, Eq, Sp, Word("uniformBalancedDeletion"), Sp, Word("hq"), Semi),
                Seq(Word("let"), Sp, Id("G"), Sp, Colon, Sp, Eq, Sp, Word("survivorGraph"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Id("D"), Semi),
                Seq(Open, Word("Function"), Dot, Word("Bijective"), Sp, LambdaLower, Sp, Id("i"), Sp, Eq, Gt),
                Seq(Word("TailRun"), Dot, Word("component"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Sp, Open, Word("uniformBalancedDeletion"), Sp, Word("hq"), Close),
                Seq(Open, Word("uniformBalancedRun"), Sp, Word("hb"), Sp, Word("hq"), Sp, Id("i"), Close, Close, Sp, Land),
                Seq(Open, Forall, Sp, Open, Id("i"), Sp, Colon, Sp, Word("Fin"), Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Close, Comma),
                Seq(Word("coe"), Open, Word("uniformBalancedRun"), Sp, Word("hb"), Sp, Word("hq"), Sp, Id("i"), Close, Dot, Word("last"), Sp, Plus, Sp, D(1), Sp, Minus, Sp, Word("coe"), Open, Word("uniformBalancedRun"), Sp, Word("hb"), Sp, Word("hq"), Sp, Id("i"), Close, Dot, Word("first"), Sp, Eq),
                Seq(Word("if"), Sp, Word("coe"), Id("i"), Sp, Eq, Sp, D(0), Sp, Word("then"), Sp, Id("q"), Sp, Minus, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Word("else"), Sp, Id("q"), Close, Sp, Land),
                Seq(Word("Fintype"), Dot, Word("card"), Sp, Id("G"), Dot, Word("ConnectedComponent"), Sp, Eq, Sp, Id("b"), Sp, Plus, Sp, D(1), Sp, Land, Sp, Forall, Sp, Open, Id("C"), Sp, Colon, Sp, Id("G"), Dot, Word("ConnectedComponent"), Close, Comma, Sp, Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Sp, Eq, Sp, Id("q"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The cut positions realize b+1 runs. The first run carries the intact prefix and its leaves, so every actual component has size q."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("component-profile-score-formulas"), DeclarationHandle.Create(Prefix + "component_profile_score_formulas"),
                H("Component profile score formulas"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("H"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("H"), Dot, Word("Adj"), CloseBracket),
                Seq(Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("let"), Sp, Id("G"), Sp, Colon, Sp, Eq, Sp, Word("survivorGraph"), Sp, Id("H"), Sp, Id("D"), Semi),
                Seq(Word("pcDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Eq, Sp, Open, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Sum, Sp, Id("C"), Comma, Sp, Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Dot, Word("choose"), Sp, D(2))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The pair sum and the largest part can be computed directly on the component supports."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-pair-target-positive"), DeclarationHandle.Create(Prefix + "balanced_pair_target_positive"),
                H("Balanced pair target positive"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Id("m"), Sp, Id("q"), Sp, Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma, Sp, D(2), Sp, Leq, Sp, Id("m"), Sp, Rightarrow, Sp, D(0), Sp, FormulaDsl.Lt, Sp, Id("q"), Sp, Rightarrow, Sp, Id("m"), Sp, Cdot, Sp, Id("q"), Sp, Leq, Sp, Id("n"), Sp, Rightarrow, Sp, Id("m"), Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Sp, FormulaDsl.Lt, Sp, Id("n"), Dot, Word("choose"), Sp, D(2)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("With at least two positive equal parts, the within-part pairs omit every cross-part pair."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scores-of-equal-component-sizes"), DeclarationHandle.Create(Prefix + "scores_of_equal_component_sizes"),
                H("Scores of equal component sizes"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("H"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("H"), Dot, Word("Adj"), CloseBracket),
                Seq(Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Sp, Open, Id("m"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(Word("Fintype"), Dot, Word("card"), Sp, Open, Word("survivorGraph"), Sp, Id("H"), Sp, Id("D"), Close, Dot, Word("ConnectedComponent"), Sp, Eq, Sp, Id("m"), Sp, Rightarrow),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Id("m"), Sp, Rightarrow),
                Seq(Open, Forall, Sp, Open, Id("C"), Sp, Colon, Sp, Open, Word("survivorGraph"), Sp, Id("H"), Sp, Id("D"), Close, Dot, Word("ConnectedComponent"), Close, Comma, Sp, Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Sp, Eq, Sp, Id("q"), Close, Sp, Rightarrow),
                Seq(Word("pcDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Eq, Sp, Open, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Id("m"), Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Sp, Land),
                Seq(Word("lccDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Eq, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Sp, Minus, Sp, Id("q"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("A component-cardinality equivalence gives the score values of the equal-part profile."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-balanced-deletion-scores"), DeclarationHandle.Create(Prefix + "uniform_balanced_deletion_scores"),
                H("Uniform balanced deletion scores"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Word("hq"), Sp, Colon, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Close, Comma),
                Seq(Word("have"), Sp, Id("n"), Sp, Colon, Sp, Eq, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Semi),
                Seq(Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Open, Word("uniformBalancedDeletion"), Sp, Word("hq"), Close, Sp, Eq),
                Seq(Id("n"), Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Sp, Land),
                Seq(Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Open, Word("uniformBalancedDeletion"), Sp, Word("hq"), Close, Sp, Eq),
                Seq(Id("n"), Sp, Minus, Sp, Id("q"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Use the b+1 components of size q to obtain both target scores."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-balanced-deletion-unique-optimizer"), DeclarationHandle.Create(Prefix + "uniform_balanced_deletion_unique_optimizer"),
                H("Uniform balanced deletion unique optimizer"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Word("hq"), Sp, Colon, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("let"), Sp, Id("H"), Sp, Colon, Sp, Eq, Sp, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Semi),
                Seq(Word("have"), Sp, Id("B"), Sp, Colon, Sp, Eq, Sp, Word("uniformBalancedDeletion"), Sp, Word("hq"), Semi),
                Seq(Word("pcDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Leq, Sp, Word("pcDamage"), Sp, Id("H"), Sp, Id("B"), Sp, Land),
                Seq(Word("lccDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Leq, Sp, Word("lccDamage"), Sp, Id("H"), Sp, Id("B"), Sp, Land),
                Seq(Open, Word("pcDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Eq, Sp, Word("pcDamage"), Sp, Id("H"), Sp, Id("B"), Sp, Lor),
                Seq(Word("lccDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Eq, Sp, Word("lccDamage"), Sp, Id("H"), Sp, Id("B"), Sp, Iff),
                Seq(Id("D"), Sp, Eq, Sp, Id("B"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Too few positive tail runs give strict comparisons. With the full count, equality requires all parts to have size q and the ordered cuts are then determined."))), DescribeRole.Theorem)),
        []));

    private static Formula Id(string name) => FormulaDsl.Id(name);

    private static Formula Word(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
}
