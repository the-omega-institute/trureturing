using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.VertexDeletion;

internal sealed class ClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/VertexDeletion/Classification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-budget classification of objective transfers involving NC.",
        H("Fixed-budget classification of transfers involving NC"),
        Blocks(
            Describe.Lean(DescribeId.Create("degree-two-common-optimizer"), DeclarationHandle.Create(Prefix + "degree_two_common_optimizer"),
                H("Degree two common optimizer"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Comma),
                Seq(Id("G"), Dot, Word("Connected"), Sp, Rightarrow),
                Seq(Id("G"), Dot, Word("maxDegree"), Sp, Leq, Sp, D(2), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Sp, Rightarrow),
                Seq(Exists, Sp, Id("D"), Comma),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Land),
                Seq(Word("ncDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Land),
                Seq(Word("pcDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Land),
                Seq(Word("lccDamage"), Sp, Id("G"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Id("G"), Close, Sp, Id("b"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("A spanning path order has at most one closing edge. Place the exact deletions so that the maximal feasible number of positive runs have balanced sizes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("degree-two-optimistic-transfers-eq-one"), DeclarationHandle.Create(Prefix + "degree_two_optimistic_transfers_eq_one"),
                H("Degree two optimistic transfers eq one"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Comma),
                Seq(Id("G"), Dot, Word("Connected"), Sp, Rightarrow),
                Seq(Id("G"), Dot, Word("maxDegree"), Sp, Leq, Sp, D(2), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Sp, Rightarrow),
                Seq(Forall, Sp, Open, Word("source"), Sp, Word("target"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(Word("source"), Sp, Eq, Sp, Word("ncDamage"), Sp, Id("G"), Sp, Lor, Sp, Word("source"), Sp, Eq, Sp, Word("pcDamage"), Sp, Id("G"), Sp, Lor, Sp, Word("source"), Sp, Eq, Sp, Word("lccDamage"), Sp, Id("G"), Sp, Rightarrow),
                Seq(Word("target"), Sp, Eq, Sp, Word("ncDamage"), Sp, Id("G"), Sp, Lor, Sp, Word("target"), Sp, Eq, Sp, Word("pcDamage"), Sp, Id("G"), Sp, Lor, Sp, Word("target"), Sp, Eq, Sp, Word("lccDamage"), Sp, Id("G"), Sp, Rightarrow),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Word("target"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("optimisticDamageRatio"), Sp, Word("source"), Sp, Word("target"), Sp, Id("b"), Sp, Eq, Sp, D(1))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("A common optimizer attains the target maximum within the source-optimal set. Each ordered pair uses its own positive target guard."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-optimizer"), DeclarationHandle.Create(Prefix + "ExactOptimizer"),
                H("Exact optimizer"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Word("score"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma, Sp, Word("ExactOptimizer"), Sp, Word("score"), Sp, Id("b"), Sp, Id("D"), Sp, Iff),
                Seq(Id("D"), Dot, Word("card"), Sp, Eq, Sp, Id("b"), Sp, Land, Sp, Word("score"), Sp, Id("D"), Sp, Eq, Sp, Word("damageMaximum"), Sp, Word("score"), Sp, Id("b"))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("The deletion has exactly b vertices and attains the maximum of the specified score."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Result"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(Forall, Sp, Open, Id("b"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(D(2), Sp, Leq, Sp, Id("b"), Sp, Rightarrow),
                Seq(Open, Forall, Sp, Open, Varepsilon, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("R"))), Close, Comma),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Rightarrow),
                Seq(Exists, Sp, Open, Id("k"), Sp, Id("q"), Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(D(1), Sp, Leq, Sp, Id("k"), Sp, Land),
                Seq(D(2), Sp, Cdot, Sp, Id("b"), Sp, Cdot, Sp, Open, Id("k"), Sp, Plus, Sp, D(2), Close, Sp, Leq, Sp, Id("q"), Sp, Land),
                Seq(Word("let"), Sp, Id("H"), Sp, Colon, Sp, Eq, Sp, Word("uniformHost"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Semi),
                Seq(Id("H"), Dot, Word("IsTree"), Sp, Land),
                Seq(Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Land),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Land),
                Seq(Forall, Sp, Open, Word("Dn"), Sp, Word("Dp"), Sp, Word("Dl"), Sp, Colon, Sp, Word("Finset"), Sp, Open, Word("UniformVertex"), Sp, Id("b"), Sp, Id("k"), Sp, Id("q"), Close, Close, Comma),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dn"), Sp, Rightarrow),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dp"), Sp, Rightarrow),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dl"), Sp, Rightarrow),
                Seq(Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dp"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dl"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("pcDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dn"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Sp, Land),
                Seq(Word("damageRatio"), Sp, Open, Word("lccDamage"), Sp, Id("H"), Close, Sp, Id("b"), Sp, Word("Dn"), Sp, FormulaDsl.Lt, Sp, Varepsilon, Close, Sp, Land),
                Seq(Open, Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close, Sp, OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket),
                Seq(Open, Delta, Sp, Colon, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(Id("G"), Dot, Word("Connected"), Sp, Rightarrow),
                Seq(Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Sp, Rightarrow),
                Seq(D(3), Sp, Leq, Sp, Delta, Sp, Rightarrow),
                Seq(Id("G"), Dot, Word("maxDegree"), Sp, Leq, Sp, Delta, Sp, Rightarrow),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Rightarrow),
                Seq(Open, Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("pcDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Sp, Rightarrow),
                Seq(D(1), Sp, Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Delta, Sp, Minus, Sp, D(1), Close, Close, Sp, Leq, Sp, Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Close, Sp, Land),
                Seq(Forall, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("lccDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Sp, Rightarrow),
                Seq(D(1), Sp, Slash, Sp, Word("coe"), Open, Id("b"), Sp, Cdot, Sp, Open, Delta, Sp, Minus, Sp, D(1), Close, Close, Sp, Leq, Sp, Word("damageRatio"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Close, Sp, Land),
                Seq(Open, Forall, Sp, Open, Word("pc"), Sp, Colon, Sp, Word("Bool"), Close, Comma, Sp, Word("sInf"), Sp, Open, Word("subcubicTreeOptimisticOutOfNC"), Sp, Id("b"), Sp, Word("pc"), Close, Sp, Eq, Sp, D(0), Close, Sp, Land),
                Seq(Forall, Sp, OpenBrace, Id("V"), Sp, Colon, Sp, Word("Type"), CloseBrace, Sp, OpenBracket, Word("DecidableEq"), Sp, Id("V"), CloseBracket, Sp, OpenBracket, Word("Fintype"), Sp, Id("V"), CloseBracket, Sp, Open, Id("G"), Sp, Colon, Sp, Word("SimpleGraph"), Sp, Id("V"), Close),
                Seq(Grp(), OpenBracket, Word("DecidableRel"), Sp, Id("G"), Dot, Word("Adj"), CloseBracket, Comma),
                Seq(Id("G"), Dot, Word("Connected"), Sp, Rightarrow),
                Seq(Id("G"), Dot, Word("maxDegree"), Sp, Leq, Sp, D(2), Sp, Rightarrow),
                Seq(Id("b"), Sp, FormulaDsl.Lt, Sp, Word("Fintype"), Dot, Word("card"), Sp, Id("V"), Sp, Rightarrow),
                Seq(Open, Exists, Sp, Open, Id("D"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Close, Comma),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("ncDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Sp, Land),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("pcDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Sp, Land),
                Seq(Word("ExactOptimizer"), Sp, Open, Word("lccDamage"), Sp, Id("G"), Close, Sp, Id("b"), Sp, Id("D"), Close, Sp, Land),
                Seq(Forall, Sp, Open, Word("source"), Sp, Word("target"), Sp, Colon, Sp, Word("Finset"), Sp, Id("V"), Sp, Rightarrow, Sp, Seq(Mathbb, Grp(Id("N"))), Close, Comma),
                Seq(Word("source"), Sp, Eq, Sp, Word("ncDamage"), Sp, Id("G"), Sp, Lor),
                Seq(Word("source"), Sp, Eq, Sp, Word("pcDamage"), Sp, Id("G"), Sp, Lor, Sp, Word("source"), Sp, Eq, Sp, Word("lccDamage"), Sp, Id("G"), Sp, Rightarrow),
                Seq(Word("target"), Sp, Eq, Sp, Word("ncDamage"), Sp, Id("G"), Sp, Lor),
                Seq(Word("target"), Sp, Eq, Sp, Word("pcDamage"), Sp, Id("G"), Sp, Lor, Sp, Word("target"), Sp, Eq, Sp, Word("lccDamage"), Sp, Id("G"), Sp, Rightarrow),
                Seq(D(0), Sp, FormulaDsl.Lt, Sp, Word("damageMaximum"), Sp, Word("target"), Sp, Id("b"), Sp, Rightarrow, Sp, Word("optimisticDamageRatio"), Sp, Word("source"), Sp, Word("target"), Sp, Id("b"), Sp, Eq, Sp, D(1))
            ]))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text("Section 9 asks “whether the constants improve on trees or on bounded-degree graphs, or whether the NC directions remain vanishing there.” The theorem settles the registered fixed-budget NC clause. One tree witnesses all four comparisons at once. At fixed degree bound at least three, inbound ratios have the stated pointwise lower bound, while both optimistic outgoing ratios have infimum zero on subcubic trees. Degree at most two gives a common exact optimizer and ratio one for every positive-target optimistic transfer. Sharp positive constants and proportional budgets remain open."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ugurlu-2026-fixed-budget-nc-transfers"), ResolutionKind.Proved))),
        []));

    private static Formula Id(string name) => FormulaDsl.Id(name);

    private static Formula Word(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
}
