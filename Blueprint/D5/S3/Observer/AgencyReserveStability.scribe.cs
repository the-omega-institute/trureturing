using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class AgencyReserveStabilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/AgencyReserveStability.agency_reserve_stability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive singular-value reserve is the sharp perturbation radius preserving an agency dimension.",
        H("Agency Reserve Stability"),
        Blocks(Describe.Lean(
            DescribeId.Create("agency-reserve-stability-and-boundary-sharpness"),
            DeclarationHandle.Create(Declaration),
            H("Reserve controls robust rank and its sharp boundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The index k is zero-based and represents the source's one-based agency "
                        + "dimension r = k + 1. This avoids truncated natural subtraction in "
                        + "the rank-at-most-(r-1) comparison class.")),
                Paragraph(Text(
                    "Eckart-Young-Mirsky and continuity of the selected singular value are "
                        + "explicit premises because pinned Mathlib supplies neither theorem. "
                        + "The low-rank set is nevertheless constructively nonempty, containing "
                        + "the zero operator.")),
                Paragraph(Text(
                    "Any smaller perturbation cannot enter the low-rank set, by the defining "
                        + "lower bound for infimum distance. An attaining best approximation "
                        + "constructs a perturbation exactly at the reserve whose selected "
                        + "singular value is zero, proving boundary sharpness.")),
                Paragraph(Text(
                    "Continuity places a neighborhood of the base point inside every safe region "
                        + "with threshold below the reserve. Mathlib's singular-value support "
                        + "theorem then keeps at least k + 1 range dimensions throughout a local "
                        + "neighborhood."))),
            DescribeRole.Theorem))));

    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(name, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula system = F.Id("H");
        Formula point = F.Id("x");
        Formula index = F.Id("k");
        Formula best = F.Id("B");
        Formula perturbation = Delta;
        Formula epsilon = F.Id("epsilon");
        Formula reserve = Call("Reserve", Call(system, point), index);
        Formula lowRank = Call("RankAtMost", index);
        Formula perturbed = Seq(Call(system, point), Sp, Plus, Sp, perturbation);
        Formula perturbedReserve = Call("Reserve", perturbed, index);
        Formula perturbedRank = Call("rank", perturbed);
        Formula safe = Call("Safe", system, index, epsilon);
        Formula y = F.Id("y");

        Formula hypotheses = Seq(
            best, Sp, InMacro, Sp, lowRank, Sp, Land, RowBreak, Grp(),
            Call("infDist", Call(system, point), lowRank), Sp, Eq, Sp, reserve, Sp, Land,
            RowBreak, Grp(),
            Call("dist", Call(system, point), best), Sp, Eq, Sp,
            Call("infDist", Call(system, point), lowRank), Sp, Land,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, reserve, Sp, Land, Sp,
            Call("ContinuousAt", Seq(Lambda, Sp, y, Dot, Sp,
                Call("Reserve", Call(system, y), index)), point));

        Formula robust = Seq(
            Forall, Sp, perturbation, Comma, Sp,
            new Formula.Norm(perturbation), Sp, Lt, Sp, reserve, Sp, Rightarrow, Sp,
            index, Sp, Plus, Sp, D(1), Sp, Leq, Sp, perturbedRank, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, perturbedReserve);
        Formula sharp = Seq(
            Exists, Sp, perturbation, Comma, Sp,
            new Formula.Norm(perturbation), Sp, Eq, Sp, reserve, Sp, Land, Sp,
            perturbedRank, Sp, Leq, Sp, index, Sp, Land, Sp,
            perturbedReserve, Sp, Eq, Sp, D(0));
        Formula neighborhoods = Seq(
            Forall, Sp, epsilon, Sp, Lt, Sp, reserve, Comma, Sp,
            Exists, Sp, F.Id("U"), Sp, InMacro, Sp, Call("N", point), Comma, Sp,
            F.Id("U"), Sp, Subseteq, Sp, safe);
        Formula localRank = Seq(
            Exists, Sp, F.Id("V"), Sp, InMacro, Sp, Call("N", point), Comma, Sp,
            Forall, Sp, y, Sp, InMacro, Sp, F.Id("V"), Comma, Sp,
            index, Sp, Plus, Sp, D(1), Sp, Leq, Sp, Call("rank", Call(system, y)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(),
            Call("Nonempty", lowRank), Sp, Land, Sp,
            Call("infDist", Call(system, point), lowRank), Sp, Eq, Sp, reserve, Sp, Land,
            RowBreak, Grp(), Open, robust, Close, Sp, Land, RowBreak, Grp(),
            Open, sharp, Close, Sp, Land, RowBreak, Grp(),
            Open, neighborhoods, Close, Sp, Land, RowBreak, Grp(),
            Open, localRank, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
