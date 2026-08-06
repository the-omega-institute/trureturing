using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class RecursiveDefinitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Dynamics/RecursiveDefinition",
                "Recursive definitions are fixed points with explicit extremal selections."),
            H("Recursive Definitions as Selected Fixed Points"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("recursive-definition-is-fixed-point"),
                    H("A recursive equation is a fixed-point equation"),
                    LeanTheorem(
                        "D5/S1/Dynamics/RecursiveDefinition.is_recursive_definition_iff_fixed_point"),
                    Disp(Seq(F.Id("f"), Open, F.Id("x"), Close, Eq, F.Id("x"), Iff, Sp, F.Id("x"), InMacro, Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For an arbitrary endomorphism and candidate value, the equation "
                        + "f(x) = x is equivalent to membership in Function.fixedPoints f.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("distinct-extremal-selections"),
                    H("Distinct extremal fixed points make the selection observable"),
                    LeanTheorem(
                        "D5/S1/Dynamics/RecursiveDefinition.extremal_selection_distinguishes_fixed_points"),
                    Disp(Seq(Operatorname, Grp(F.Id("lfp")), Open, F.Id("f"), Close, Neq, Operatorname, Grp(F.Id("gfp")), Open, F.Id("f"), Close, Rightarrow, Sp, F.Id("f"), Open, Operatorname, Grp(F.Id("select")), Underscore, F.Id("f"), Open, Mathrm, Grp(F.Id("least")), Close, Close, Eq, Operatorname, Grp(F.Id("select")), Underscore, F.Id("f"), Open, Mathrm, Grp(F.Id("least")), Close, Land, Sp, F.Id("f"), Open, Operatorname, Grp(F.Id("select")), Underscore, F.Id("f"), Open, Mathrm, Grp(F.Id("greatest")), Close, Close, Eq, Operatorname, Grp(F.Id("select")), Underscore, F.Id("f"), Open, Mathrm, Grp(F.Id("greatest")), Close, Land, Sp, Operatorname, Grp(F.Id("select")), Underscore, F.Id("f"), Open, Mathrm, Grp(F.Id("least")), Close, Neq, Operatorname, Grp(F.Id("select")), Underscore, F.Id("f"), Open, Mathrm, Grp(F.Id("greatest")), Close, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The selector is explicit data with least and greatest cases. For a "
                        + "monotone endomorphism of a complete lattice, if its least and greatest "
                        + "fixed points differ, both selected values satisfy the fixed-point "
                        + "equation and the two selected values are unequal.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("unique-fixed-point-collapses-extremes"),
                    H("Uniqueness identifies the least and greatest fixed points"),
                    LeanTheorem(
                        "D5/S1/Dynamics/RecursiveDefinition.unique_fixed_point_implies_lfp_eq_gfp"),
                    Disp(Seq(Left, Open, Exists, Bang, F.Id("x"), Comma, Esc, F.Id("f"), Open, F.Id("x"), Close, Eq, F.Id("x"), Right, Close, Rightarrow, Sp, Operatorname, Grp(F.Id("lfp")), Open, F.Id("f"), Close, Eq, Operatorname, Grp(F.Id("gfp")), Open, F.Id("f"), Close, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a monotone endomorphism of a complete lattice, the existence of "
                        + "exactly one value satisfying f(x) = x implies that the least and "
                        + "greatest fixed points coincide.")))
                )),
[
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Dynamics/RecursiveDefinition.extremal_selection_distinguishes_fixed_points")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Dynamics/RecursiveDefinition.is_recursive_definition_iff_fixed_point")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Dynamics/RecursiveDefinition.unique_fixed_point_implies_lfp_eq_gfp")),
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Dynamics/KnasterTarski")),
                    ]));
}
