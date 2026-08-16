using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class ThreeCycleFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An order-three permutation on a finite set of size one modulo three has a fixed point.",
        H("A Fixed Point Forced by Three-Cycle Counting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-cycle-cardinality-forces-a-fixed-point"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/ThreeCycleFixedPoint."
                    + "three_cycle_action_has_fixed_point"),
                H("Three-cycle cardinality forces a fixed point"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let sigma be a permutation of a finite set X. If sigma cubed is the "
                        + "identity, every nontrivial orbit has three elements. Consequently, "
                        + "card(X) congruent to one modulo three forces a singleton orbit and "
                        + "therefore a fixed point.")),
                    Paragraph(Text(
                        "The Lean proof specializes the pinned Mathlib theorem "
                        + "Equiv.Perm.exists_fixed_point_of_prime at the prime three. The only "
                        + "local step converts card(X) modulo three equal to one into the "
                        + "theorem's nondivisibility hypothesis.")),
                    Paragraph(Text(
                        "This closes only the fixed-point consequence in the P3 clause of source "
                        + "remark 27.583. It does not assert the constant-law identities, the P1 "
                        + "or P2 predictions, the numerical search outcome, or the engineering "
                        + "postmortem elsewhere in the atom."))),
                DescribeRole.Theorem))));

    private static Formula FixedPointFormula()
    {
        Formula carrier = F.Id("X");
        Formula sigma = F.Id("sigma");
        Formula point = F.Id("x");
        Formula identity = F.Id("id");
        Formula cardinality = Seq(
            Operatorname, Grp(F.Id("card")), Open, carrier, Close);

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp, sigma, Comma, Esc,
            new Formula.Power(sigma, D(3)), Eq, identity, Sp, Land, Sp,
            new Formula.Modulo(cardinality, D(3)), Eq, D(1), Sp,
            Rightarrow, Sp, Exists, Sp, point, InMacro, Sp, carrier, Comma, Esc,
            sigma, Open, point, Close, Eq, point, Dot));
    }
}
