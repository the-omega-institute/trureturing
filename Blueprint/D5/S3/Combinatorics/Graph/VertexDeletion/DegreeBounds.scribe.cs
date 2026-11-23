using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.VertexDeletion;

internal sealed class DegreeBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/VertexDeletion/DegreeBounds.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/ugurlu2026objectivetransfer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree bounds and positive-target optimistic ratios for exact cuts.",
        H("NC transfer bounds under degree constraints"),
        Blocks(
            Describe.Lean(DescribeId.Create("survivor-card"), DeclarationHandle.Create(Prefix + "survivor_card"),
                H("Survivor card"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("Fintype"), Dot, Word("card"), Sp, Word("coe"), Open, Word("survivors"), Sp, Id("D"), Close, Sp, Eq, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Sp, Minus, Sp, Id("D"), Dot, Word("card"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The survivors are the complement of the deletion finset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("component-card-eq"), DeclarationHandle.Create(Prefix + "component_card_eq"),
                H("Component card eq"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket),
                Seq(Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Open, Word("componentSizes"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("card"), Sp, Eq, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("survivorGraph"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("ConnectedComponent"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The size multiset has one entry per actual survivor component."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nc-le-budget-mul-degree-sub-one"), DeclarationHandle.Create(Prefix + "nc_le_budget_mul_degree_sub_one"),
                H("Nc le budget mul degree sub one"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Comma),
                Seq(Id("G"), Dot, Word("Connected"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Delta, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, Id("G"), Dot, Word("maxDegree"), Sp, Leq, Sp, Delta, Sp, Rightarrow, Sp, Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma, Sp, Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow, Sp, Word("ncDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Leq, Sp, Id("b"), Sp, Cdot, Sp, Open, Delta, Sp, Minus, Sp, D(1), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Charge every non-root survivor component to an incident deleted vertex closer to a surviving root. Every deleted vertex also has a closer neighbor outside its available charges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bounded-degree-transfers-into-nc"), DeclarationHandle.Create(Prefix + "bounded_degree_transfers_into_nc"),
                H("Bounded degree transfers into nc"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Comma),
                Seq(Id("G"), Dot, Word("Connected"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Delta, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(Id("G"), Dot, Word("maxDegree"), Sp, Leq, Sp, Delta, Sp, Rightarrow),
                Seq(Forall, Sp, Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Comma),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Open, Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("pcDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Delta, Sp, Minus, Sp, D(1), Close, Close, Sp, Leq, Sp, Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Close, Sp, Land),
                Seq(Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("lccDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Delta, Sp, Minus, Sp, D(1), Close, Close, Sp, Leq, Sp, Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Every PC and LCC maximizer disconnects the survivors when a positive NC value is attainable. The component bound controls the common denominator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inst-decidable-uniform-host-adj"), DeclarationHandle.Create(Prefix + "instDecidableUniformHostAdj"),
                H("Inst decidable uniform host adj"), StatementSource.FromAuthor(Disp(Seq(Word("instDecidableUniformHostAdj"), Sp, Colon, Sp, Open, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Rightarrow, Sp, Word("DecidableRel"), Sp, Open, Word("uniformHost"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Dot, Word("Adj")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Decide adjacency by the spine-edge test or the prescribed leaf incidence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("subcubic-tree-out-of-nc-arbitrarily-small"), DeclarationHandle.Create(Prefix + "subcubic_tree_out_of_nc_arbitrarily_small"),
                H("Subcubic tree out of nc arbitrarily small"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("R"))), Close, Comma),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Rightarrow),
                Seq(Exists, Sp, Id("q"), Comma),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, D(1), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Land),
                Seq(Word("let"), Sp, Id("H"), Sp, Colon, Sp, Eq, Sp, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Semi),
                Seq(Id("H"), Dot, Word("IsTree"), Sp, Land),
                Seq(Id("H"), Dot, Word("maxDegree"), Sp, Leq, Sp, D(3), Sp, Land),
                Seq(Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, D(1), Sp, Id("q"), Close, Sp, Land),
                Seq(Open, D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Close, Sp, Land),
                Seq(Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, D(1), Sp, Id("q"), Close, Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("ncDamage"), Sp, Id("H"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("damageRatio"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Id("D"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Id("D"), Sp, FormulaDsl.Lt, Sp, Varepsilon)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("One leaf per hub gives maximum degree at most three. Increasing the tail makes both outgoing NC comparisons small for every exact NC optimizer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-tree-simultaneous-epsilon"), DeclarationHandle.Create(Prefix + "uniform_tree_simultaneous_epsilon"),
                H("Uniform tree simultaneous epsilon"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("R"))), Close, Comma),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Rightarrow),
                Seq(Exists, Sp, Id("k"), Sp, Id("q"), Comma),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Land),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Land),
                Seq(Word("let"), Sp, Id("H"), Sp, Colon, Sp, Eq, Sp, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Semi),
                Seq(Id("H"), Dot, Word("IsTree"), Sp, Land),
                Seq(Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Land),
                Seq(Open, D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Close, Sp, Land),
                Seq(Forall, Sp, Open, Word("Dn"), Sp, Word("Dp"), Sp, Word("Dl"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma),
                Seq(Word("Dn"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("Dp"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("Dl"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("ncDamage"), Sp, Id("H"), Sp, Word("Dn"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("pcDamage"), Sp, Id("H"), Sp, Word("Dp"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("lccDamage"), Sp, Id("H"), Sp, Word("Dl"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dp"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dl"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dn"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dn"), Sp, FormulaDsl.Lt, Sp, Varepsilon)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Every spine edge and leaf edge is a bridge. This certifies that the common witness for all four strict comparisons is a tree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("optimistic-damage-ratio"), DeclarationHandle.Create(Prefix + "optimisticDamageRatio"),
                H("Optimistic damage ratio"), StatementSource.FromAuthor(Disp(Seq(Word("optimisticDamageRatio"), Sp, Colon, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, Rightarrow, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Rightarrow, Sp, Open, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Rightarrow, Sp, Open, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("R")))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(DefinitionDsl.Text("Section 2 resolves source ties by maximizing the attained target score over the exact source optimizers. The denominator is the exact target maximum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("optimistic-ratio-eq-one-of-common"), DeclarationHandle.Create(Prefix + "optimistic_ratio_eq_one_of_common"),
                H("Optimistic ratio eq one of common"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Word("source"), Sp, Word("target"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("source"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Word("source"), Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("target"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Word("target"), Sp, Id("b"), Sp, Rightarrow),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Word("target"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("optimisticDamageRatio"), Sp, Word("source"), Sp, Word("target"), Sp, Id("b"), Sp, Eq, Sp, D(1))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("A source optimizer that also attains the target maximum makes that value attainable in the optimistic numerator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("subcubic-tree-optimistic-out-of-nc"), DeclarationHandle.Create(Prefix + "subcubicTreeOptimisticOutOfNC"),
                H("Subcubic tree optimistic out of nc"), StatementSource.FromAuthor(Disp(Seq(Word("subcubicTreeOptimisticOutOfNC"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Sp, Rightarrow, Sp, Word("Bool"), Sp, Rightarrow, Sp, Word("Set"), Sp, Seq(Mathbb, Grp(Id("R")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The Boolean selects PC when true and LCC when false. The set uses finite trees of maximum degree at most three and requires positivity for the selected target."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("subcubic-tree-optimistic-out-of-nc-infimum-zero"), DeclarationHandle.Create(Prefix + "subcubic_tree_optimistic_out_of_nc_infimum_zero"),
                H("Subcubic tree optimistic out of nc infimum zero"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma, Sp, D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow, Sp, Forall, Sp, Open, Word("pc"), Sp, Colon, Sp, Word("Bool"), Close, Comma, Sp, Word("sInf"), Sp, Open, Word("subcubicTreeOptimisticOutOfNC"), Sp, Id("b"), Sp, Word("pc"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("All ratios are nonnegative. The one-leaf trees give a member below every positive threshold."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-optimizer-of-balanced-maximal-profile"), DeclarationHandle.Create(Prefix + "common_optimizer_of_balanced_maximal_profile"),
                H("Common optimizer of balanced maximal profile"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket),
                Seq(Open, Id("b"), Sp, Id("m"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("Fintype"), Dot, Word("card"), Sp, Open, Word("survivorGraph"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("ConnectedComponent"), Sp, Eq, Sp, Id("m"), Sp, Rightarrow),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Id("m"), Sp, Rightarrow),
                Seq(Open, Forall, Sp, Open, Id("C"), Sp, Colon, Sp, Open, Word("survivorGraph"), Sp, Id("G"), Sp, Id("D"), Close, Dot, Word("ConnectedComponent"), Close, Comma),
                Seq(Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Sp, Eq, Sp, Id("q"), Sp, Lor, Sp, Id("C"), Dot, Word("supp"), Dot, Word("toFinset"), Dot, Word("card"), Sp, Eq, Sp, Id("q"), Sp, Plus, Sp, D(1), Close, Sp, Rightarrow),
                Seq(Open, Forall, Sp, Open, Id("E"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma, Sp, Id("E"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("survivorGraph"), Sp, Id("G"), Sp, Id("E"), Close, Dot, Word("ConnectedComponent"), Sp, Leq, Sp, Id("m"), Close, Sp, Rightarrow),
                Seq(Word("ncDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Land),
                Seq(Word("pcDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Land),
                Seq(Word("lccDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Id("G"), Close, Sp, Id("b"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The maximal feasible number of runs and sizes differing by at most one simultaneously bound the largest part and minimize the sum of within-component pairs."))), DescribeRole.Theorem)),
        []));

    private static Formula Id(string name) => FormulaDsl.Id(name);

    private static Formula Word(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
}
