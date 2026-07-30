using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class KnasterTarskiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Dynamics/KnasterTarski",
                "Monotone endomorphisms have extremal fixed points, separated by a three-state cycle."),
            H("Knaster-Tarski Extremal Fixed Points"),
            Blocks(
                new DocumentBlock.Describe(
                    DescribeId.Create("least-and-greatest-fixed-points"),
                    DescribeKind.Theorem,
                    H("Least and greatest fixed points"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Dynamics/KnasterTarski.knaster_tarski_extremal_fixed_points")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The classical Knaster-Tarski theorem states that every monotone "
                            + "endomorphism of a complete lattice has a least fixed point and a "
                            + "greatest fixed point. The Lean declaration is an honest "
                            + "repository wrapper around Mathlib's least and greatest fixed-point "
                            + "constructions and their extremality theorems. No repository "
                            + "literature note currently attests the classical source, so the "
                            + "provenance is conservatively recorded as repository-derived rather "
                            + "than literature-attested.")),
                        Paragraph(Text(
                            "On the three-state successor cycle, the induced powerset operator is "
                            + "inverse image under succession. It preserves the empty set and the "
                            + "full carrier; extremality therefore identifies the least fixed point "
                            + "with the empty set and the greatest fixed point with the full set. "
                            + "The inductive interpretation has no grounded state from which to "
                            + "begin, whereas the coinductive interpretation accepts the entire "
                            + "self-sustaining cycle."))),
                    LatexStatement.Create(
                        @"$$f:L\to L\ \text{monotone}\Rightarrow "
                        + @"\mu=\operatorname{lfp}(f)=\min\operatorname{Fix}(f),\ "
                        + @"\nu=\operatorname{gfp}(f)=\max\operatorname{Fix}(f);\qquad "
                        + @"F(X)=\{s\mid\operatorname{succ}(s)\in X\}\Rightarrow "
                        + @"\operatorname{lfp}(F)=\varnothing,\ "
                        + @"\operatorname{gfp}(F)=S.$$")))));
}
