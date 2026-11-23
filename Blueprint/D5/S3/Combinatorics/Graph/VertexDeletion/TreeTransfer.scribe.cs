using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.VertexDeletion;

internal sealed class TreeTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/VertexDeletion/TreeTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact hub and balanced optimizers yield four small transfer ratios.",
        H("Exact optimizers on the tree with pendant leaves"),
        Blocks(
            Describe.Lean(DescribeId.Create("host-hub"), DeclarationHandle.Create(Prefix + "hostHub"),
                H("Host hub"), StatementSource.FromAuthor(Disp(Seq(Word("hostHub"), Sp, Colon, Sp, OpenBrace, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Sp, Rightarrow, Sp, Open, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("p"), Close, Sp, Rightarrow, Sp, Word("Fin"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("Vertex"), Sp, Id("p"), Sp, Id("t"), Sp, Id("b"), Sp, Id("k")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Include the specified hub in the spine summand of the host carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("component-eq-iff-of-no-adj"), DeclarationHandle.Create(Prefix + "component_eq_iff_of_no_adj"),
                H("Component eq iff of no adj"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBrace, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), CloseBrace, Sp, OpenBrace, Id("v"), Sp, Colon, Sp, Id("V"), CloseBrace, Comma),
                Seq(Open, Forall, Sp, Open, Id("w"), Sp, Colon, Sp, Id("V"), Close, Comma, Sp, Neg, Sp, Id("G"), Dot, Word("Adj"), Sp, Id("v"), Sp, Id("w"), Close, Sp, Rightarrow, Sp, Forall, Sp, Open, Id("w"), Sp, Colon, Sp, Id("V"), Close, Comma, Sp, Id("G"), Dot, Word("connectedComponentMk"), Sp, Id("v"), Sp, Eq, Sp, Id("G"), Dot, Word("connectedComponentMk"), Sp, Id("w"), Sp, Iff, Sp, Id("v"), Sp, Eq, Sp, Id("w"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Distinct reachable vertices have incident edges, so the component of an isolated vertex is a singleton."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-hub-deletion-unique-nc-optimizer"), DeclarationHandle.Create(Prefix + "uniform_hub_deletion_unique_nc_optimizer"),
                H("Uniform hub deletion unique nc optimizer"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Id("D"), Sp, Leq),
                Seq(Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close),
                Seq(Open, Word("uniformHubDeletion"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Land),
                Seq(Open, Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Id("D"), Sp, Eq),
                Seq(Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close),
                Seq(Open, Word("uniformHubDeletion"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Iff),
                Seq(Id("D"), Sp, Eq, Sp, Word("uniformHubDeletion"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Each deleted hub can detach its k leaves. Equality in the component bound requires every deletion to be a hub."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-order"), DeclarationHandle.Create(Prefix + "uniform_order"),
                H("Uniform order"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Eq, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Sp, Plus, Sp, Id("b")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Add the exact deletion budget to the survivor count."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("damage-maximum-eq-of-dominates"), DeclarationHandle.Create(Prefix + "damageMaximum_eq_of_dominates"),
                H("Damage maximum eq of dominates"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Word("score"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow, Sp, Open, Forall, Sp, Open, Id("E"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma, Sp, Id("E"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow, Sp, Word("score"), Sp, Id("E"), Sp, Leq, Sp, Word("score"), Sp, Id("D"), Close, Sp, Rightarrow, Sp, Word("damageMaximum"), Sp, Word("score"), Sp, Id("b"), Sp, Eq, Sp, Word("score"), Sp, Id("D"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("An attained pointwise maximum is the supremum over the exact-budget cuts."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-exact-budget-maxima"), DeclarationHandle.Create(Prefix + "uniform_exact_budget_maxima"),
                H("Uniform exact budget maxima"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Word("hq"), Sp, Colon, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Close, Comma),
                Seq(Open, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Eq),
                Seq(Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close),
                Seq(Open, Word("uniformHubDeletion"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Land),
                Seq(Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Eq),
                Seq(Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close),
                Seq(Open, Word("uniformBalancedDeletion"), Sp, Word("hq"), Close, Sp, Land),
                Seq(Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Eq),
                Seq(Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close),
                Seq(Open, Word("uniformBalancedDeletion"), Sp, Word("hq"), Close, Close, Sp, Land),
                Seq(Open, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Eq),
                Seq(Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(1), Close, Sp, Land),
                Seq(Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Eq),
                Seq(Open, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Sp, Plus, Sp, Id("b"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Sp, Land),
                Seq(Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Eq),
                Seq(Id("b"), Sp, Cdot, Sp, Open, Id("q"), Sp, Plus, Sp, D(1), Close, Close, Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Use the unique hub optimizer for NC and the unique balanced optimizer for both other scores."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("damage-ratio"), DeclarationHandle.Create(Prefix + "damageRatio"),
                H("Damage ratio"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Word("target"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma, Sp, Word("damageRatio"), Sp, Word("target"), Sp, Id("b"), Sp, Id("D"), Sp, Eq),
                Seq(Open, Word("coe"), Open, Word("target"), Sp, Id("D"), Close, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("R"))), Close, Sp, Slash, Sp, Word("coe"), Open, Word("damageMaximum"), Sp, Word("target"), Sp, Id("b"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The value at this deletion is divided by the exact-budget maximum for the target score. The classification imposes a positive target maximum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-transfer-identities"), DeclarationHandle.Create(Prefix + "uniform_transfer_identities"),
                H("Uniform transfer identities"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Rightarrow),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Word("Dn"), Sp, Word("Dp"), Sp, Word("Dl"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma),
                Seq(Word("Dn"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("Dp"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("Dl"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Word("Dn"), Sp, Eq),
                Seq(Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Word("Dp"), Sp, Eq),
                Seq(Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Sp, Word("Dl"), Sp, Eq),
                Seq(Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close),
                Seq(Id("b"), Sp, Rightarrow),
                Seq(Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b")),
                Seq(Word("Dp"), Sp, Eq),
                Seq(D(1), Sp, Slash, Sp, Open, Word("coe"), Id("k"), Sp, Plus, Sp, D(1), Close, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close, Sp, Id("b")),
                Seq(Word("Dl"), Sp, Eq),
                Seq(D(1), Sp, Slash, Sp, Open, Word("coe"), Id("k"), Sp, Plus, Sp, D(1), Close, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("lccDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close),
                Seq(Id("b"), Sp, Word("Dn"), Sp, Eq),
                Seq(Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Close, Sp, Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Id("q"), Sp, Plus, Sp, D(1), Close, Close, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("pcDamage"), Sp, Open, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Close, Close),
                Seq(Id("b"), Sp, Word("Dn"), Sp, Eq),
                Seq(Word("coe"), Open, Open, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Sp, Plus, Sp, Id("b"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Word("uniformTailLength"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Dot, Word("choose"), Sp, D(2), Close, Sp, Slash),
                Seq(Word("coe"), Open, Open, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Sp, Plus, Sp, Id("b"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Optimizer uniqueness fixes the denominator and the source cut in each of the four evaluations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-pc-transfer-bound"), DeclarationHandle.Create(Prefix + "uniform_pc_transfer_bound"),
                H("Uniform pc transfer bound"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow),
                Seq(Word("coe"), Open, Open, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Sp, Plus, Sp, Id("b"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Word("uniformTailLength"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Dot, Word("choose"), Sp, D(2), Close, Sp, Slash),
                Seq(Word("coe"), Open, Open, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Sp, Plus, Sp, Id("b"), Close, Dot, Word("choose"), Sp, D(2), Sp, Minus, Sp, Open, Id("b"), Sp, Plus, Sp, D(1), Close, Sp, Cdot, Sp, Id("q"), Dot, Word("choose"), Sp, D(2), Close, Sp, Leq),
                Seq(Word("coe"), Open, D(4), Sp, Cdot, Sp, Open, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Close, Close, Sp, Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Id("q"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Compare the PC damage from the hub cut with the positive balanced optimum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-lcc-transfer-bound"), DeclarationHandle.Create(Prefix + "uniform_lcc_transfer_bound"),
                H("Uniform lcc transfer bound"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("b"), Sp, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), CloseBrace, Comma, Sp, D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow, Sp, D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Rightarrow, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Close, Sp, Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Id("q"), Sp, Plus, Sp, D(1), Close, Close, Sp, Leq, Sp, Word("coe"), Open, D(4), Sp, Cdot, Sp, Open, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Close, Close),
                Seq(Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Id("q"), Close)
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Compare the largest survivor under the hub cut with the balanced target optimum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-simultaneous-epsilon"), DeclarationHandle.Create(Prefix + "uniform_simultaneous_epsilon"),
                H("Uniform simultaneous epsilon"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("R"))), Close, Comma),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Rightarrow),
                Seq(Exists, Sp, Id("k"), Sp, Id("q"), Comma),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Land),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Land),
                Seq(Word("let"), Sp, Id("H"), Sp, Colon, Sp, Eq, Sp, Word("host"), Sp, Open, Word("uniformHub"), Sp, Id("b"), Close, Semi),
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
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Choose k for the two inbound comparisons and then q for the two outgoing comparisons on the same host."))), DescribeRole.Theorem)),
        []));

    private static Formula Id(string name) => FormulaDsl.Id(name);

    private static Formula Word(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
}
