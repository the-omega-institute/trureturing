using static StrataLint.Scribe.DefinitionDsl;

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
                new DocumentBlock.Describe(
                    DescribeId.Create("recursive-definition-is-fixed-point"),
                    DescribeKind.Theorem,
                    H("A recursive equation is a fixed-point equation"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Dynamics/RecursiveDefinition.is_recursive_definition_iff_fixed_point")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For an arbitrary endomorphism and candidate value, the equation "
                        + "f(x) = x is equivalent to membership in Function.fixedPoints f."))),
                    LatexStatement.Create(
                        @"$$f(x)=x\iff x\in\operatorname{Fix}(f).$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("distinct-extremal-selections"),
                    DescribeKind.Theorem,
                    H("Distinct extremal fixed points make the selection observable"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Dynamics/RecursiveDefinition.extremal_selection_distinguishes_fixed_points")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The selector is explicit data with least and greatest cases. For a "
                        + "monotone endomorphism of a complete lattice, if its least and greatest "
                        + "fixed points differ, both selected values satisfy the fixed-point "
                        + "equation and the two selected values are unequal."))),
                    LatexStatement.Create(
                        @"$$\operatorname{lfp}(f)\neq\operatorname{gfp}(f)\Longrightarrow "
                        + @"f(\operatorname{select}_f(\mathrm{least}))="
                        + @"\operatorname{select}_f(\mathrm{least})\land "
                        + @"f(\operatorname{select}_f(\mathrm{greatest}))="
                        + @"\operatorname{select}_f(\mathrm{greatest})\land "
                        + @"\operatorname{select}_f(\mathrm{least})\neq"
                        + @"\operatorname{select}_f(\mathrm{greatest}).$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("unique-fixed-point-collapses-extremes"),
                    DescribeKind.Theorem,
                    H("Uniqueness identifies the least and greatest fixed points"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Dynamics/RecursiveDefinition.unique_fixed_point_implies_lfp_eq_gfp")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a monotone endomorphism of a complete lattice, the existence of "
                        + "exactly one value satisfying f(x) = x implies that the least and "
                        + "greatest fixed points coincide."))),
                    LatexStatement.Create(
                        @"$$\left(\exists!x,\ f(x)=x\right)\Longrightarrow "
                        + @"\operatorname{lfp}(f)=\operatorname{gfp}(f).$$")))));
}
