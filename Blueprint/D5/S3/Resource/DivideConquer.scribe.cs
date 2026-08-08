using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class DivideConquerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Resource/DivideConquer",
            "Subadditivity of infimum-defined resource functionals under feasible additive product strategies."),
        H("The Divide-Conquer Lemma for Resource Functionals"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("tensor-closed-infimum-resource-functionals-are-subadditive"),
                H("Tensor-closed infimum resource functionals are subadditive"),
                LeanTheorem(
                    "D5/S3/Resource/DivideConquer.resource_functional_subadditive"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    F.Id("F"), Open, F.Id("X"), Close, Colon, Eq, Sp,
                    Operatorname, Grp(F.Id("inf")), Underscore, Grp(
                        F.Id("s"), Colon, Sp,
                        Operatorname, Grp(F.Id("feasible")),
                        Open, F.Id("s"), Comma, Sp, F.Id("X"), Close),
                    Sp, F.Id("c"), Open, F.Id("s"), Close, Comma, RowBreak,
                    Open,
                    Operatorname, Grp(F.Id("feasible")),
                    Open, F.Id("s"), Underscore, Grp(F.Id("X")), Comma, Sp,
                    F.Id("X"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("feasible")),
                    Open, F.Id("s"), Underscore, Grp(F.Id("Y")), Comma, Sp,
                    F.Id("Y"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("feasible")), Open,
                    Operatorname, Grp(F.Id("tensorStrat")), Open,
                    F.Id("s"), Underscore, Grp(F.Id("X")), Comma, Sp,
                    F.Id("s"), Underscore, Grp(F.Id("Y")), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("tensorObj")), Open,
                    F.Id("X"), Comma, Sp, F.Id("Y"), Close, Close,
                    Close, Sp, Land, Sp, RowBreak,
                    Open,
                    F.Id("c"), Open,
                    Operatorname, Grp(F.Id("tensorStrat")), Open,
                    F.Id("s"), Underscore, Grp(F.Id("X")), Comma, Sp,
                    F.Id("s"), Underscore, Grp(F.Id("Y")), Close, Close,
                    Eq,
                    F.Id("c"), Open, F.Id("s"), Underscore, Grp(F.Id("X")), Close,
                    Plus,
                    F.Id("c"), Open, F.Id("s"), Underscore, Grp(F.Id("Y")), Close,
                    Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("F"), Open,
                    Operatorname, Grp(F.Id("tensorObj")), Open,
                    F.Id("X"), Comma, Sp, F.Id("Y"), Close, Close,
                    Sp, Le, Sp,
                    F.Id("F"), Open, F.Id("X"), Close,
                    Plus,
                    F.Id("F"), Open, F.Id("Y"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let Obj be a type of resource objects and Strat a type of strategies. " +
                        "The data include tensorObj on objects, tensorStrat on strategies, a " +
                        "feasibility predicate, and a cost valued in the extended nonnegative " +
                        "reals. The two structural hypotheses are explicit: tensorStrat(sX,sY) " +
                        "is feasible for tensorObj(X,Y) whenever sX and sY are feasible for X " +
                        "and Y, and its cost is exactly c(sX)+c(sY). The functional F is the " +
                        "infimum of c over the feasible-strategy subtype.")),
                    Paragraph(Text(
                        "For every feasible pair sX and sY, the product strategy is an admissible " +
                        "competitor for tensorObj(X,Y). Therefore F(tensorObj(X,Y)) is at most " +
                        "c(tensorStrat(sX,sY)), which the additive-cost hypothesis identifies " +
                        "with c(sX)+c(sY). Mathlib's ENNReal.le_iInf_add_iInf then takes both " +
                        "infima and yields the displayed subadditivity inequality. Since costs " +
                        "lie in the extended nonnegative reals, an empty feasible class has " +
                        "value infinity; the same lattice lemma covers that boundary without " +
                        "an auxiliary nonemptiness or boundedness assumption.")))))));
}
