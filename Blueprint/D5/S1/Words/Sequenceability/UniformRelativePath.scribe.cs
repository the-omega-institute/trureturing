using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class UniformRelativePathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite-path consequences of a whole-carrier cycle and two inventories.",
        H("Whole-carrier cycle to relative path"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-relative-path-composition"),
            DeclarationHandle.Create("D5/S1/Words/Sequenceability/UniformRelativePath.compose_full_path"),
            H("Cycle composition gives every path clause"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let X be finite and G an additive commutative group. "
                    + "Suppose Q is a single cycle on X, with coordinate map coord, "
                    + "endpoints s,t, and Q(t)=s. If |X|=M+1, the orbit "
                    + "coord(Q^n(s)) for 0<=n<=M is the actual path with M labels.")),
                Paragraph(Text("The hypotheses retain the exact coordinate inventory on "
                    + "X minus the two endpoints and the exact label inventory on "
                    + "X minus t. The theorem transports these inventories along the "
                    + "actual orbit, so it proves the endpoint values, distinct actual "
                    + "vertices, interior bijection, and label bijection without a "
                    + "count-only argument.")),
                Paragraph(Text("Finite-cycle injectivity makes every bounded coefficient-one "
                    + "prefix distinct after telescoping. The same telescoping identity "
                    + "turns every nonempty bounded interval into a difference of two "
                    + "distinct path vertices, hence nonzero, and the full sum is the "
                    + "prescribed endpoint displacement. This is the reusable composition "
                    + "layer for the universal finite-field construction; the affine lift, "
                    + "whole-set surgery, and characteristic-five boundary must still "
                    + "supply its hypotheses."))),
            DescribeRole.Theorem)),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-relative-path-characteristic-five"),
            DeclarationHandle.Create("D5/S1/Words/Sequenceability/UniformRelativePath.characteristic_five_case"),
            H("Published characteristic-five path transported into the universal namespace"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The characteristic-five branch delegates to the published "
                + "three-cut detour theorem, preserving its exact vertex and full-vector label "
                + "inventories, endpoints, bounded prefixes, intervals, and total. The remaining "
                + "universal branch must instantiate the affine chart from the rotational column "
                + "triple and prove the whole-carrier surgery cycle for every prime p>=7."))),
            DescribeRole.Theorem))));
}
