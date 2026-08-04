using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("least-and-greatest-fixed-points"),
                    H("Least and greatest fixed points"),
                    LeanTheorem(
                        "D5/S1/Dynamics/KnasterTarski.knaster_tarski_extremal_fixed_points"),
                    Disp(Seq(F.Id("f"), Colon, F.Id("L"), To, Sp, F.Id("L"), Esc, F.Text, Grp(F.Id("monotone")), Rightarrow, Sp, Mu, Eq, Operatorname, Grp(F.Id("lfp")), Open, F.Id("f"), Close, Eq, Min, Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Comma, Esc, Nu, Eq, Operatorname, Grp(F.Id("gfp")), Open, F.Id("f"), Close, Eq, Max, Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Dot)),
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
                            + "than literature-attested.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("three-state-successor-cycle"),
                    H("Three-state successor cycle"),
                    LeanTheorem(
                        "D5/S1/Dynamics/KnasterTarski.three_cycle_extremal_fixed_points"),
                    Disp(Seq(F.Id("F"), Open, F.Id("X"), Close, Eq, OpenBrace, F.Id("s"), Mid, Operatorname, Grp(F.Id("succ")), Open, F.Id("s"), Close, InMacro, Sp, F.Id("X"), CloseBrace, Rightarrow, Sp, Operatorname, Grp(F.Id("lfp")), Open, F.Id("F"), Close, Eq, Varnothing, Comma, Esc, Operatorname, Grp(F.Id("gfp")), Open, F.Id("F"), Close, Eq, F.Id("S"), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "On the three-state successor cycle, the induced powerset operator is "
                            + "inverse image under succession. It preserves the empty set and the "
                            + "full carrier; extremality therefore identifies the least fixed point "
                            + "with the empty set and the greatest fixed point with the full set. "
                            + "The inductive interpretation has no grounded state from which to "
                            + "begin, whereas the coinductive interpretation accepts the entire "
                            + "self-sustaining cycle.")))
                ))));
}
