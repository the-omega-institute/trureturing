using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class NormalSubgroupFixedMassDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass."
        + "maximal_normal_subgroup_fixed_seed_mass";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum fixed seed mass for a normal subgroup of the acting group.",
        H("Normal subgroup fixed seed mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-normal-subgroup-fixed-seed-mass"),
                DeclarationHandle.Create(Gid),
                H("The least row bound is attained under the full group action"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A group G acts on a nonempty finite input set X and a finite output set Y. "
                        + "Let H be a normal subgroup of G. The probability kernel P is covariant "
                        + "under G. The H row mass sums P over outputs fixed by all elements of H "
                        + "that fix that input.")),
                    Paragraph(Text(
                        "The same minimizing row bounds the total weight of H-fixed seeds of "
                        + "every finite calibration with nonnegative weights and a G-covariant "
                        + "readout. There is an attaining finite calibration with positive weights "
                        + "summing to one, invariant under G, with all marginals equal to P.")),
                    Paragraph(Text(
                        "Apply the full-group fixed mass theorem to H. Send each seed to its "
                        + "deterministic table. The table law has the required marginals, and "
                        + "every H-fixed seed maps to an H-fixed table. Average this law over "
                        + "the finite image of G acting on the table space. Covariance preserves "
                        + "the marginals in each translated law. Normality ensures that each "
                        + "translate preserves the set of H-fixed tables. Restrict to the "
                        + "positive support of the averaged law and use the row bound to obtain equality."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula h = F.Id("H");
        Formula p = F.Id("P");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula row = Call("RowFixedMass", h, p, x);
        return Disp(Seq(Forall, Sp, h, Comma, Sp, p, Comma, Sp, Call("Normal", h),
            Sp, Land, Sp, Call("CovariantProbabilityKernel", p),
            Sp, Rightarrow, Sp, Exists, Sp, x, Comma, Sp,
            Open, Forall, Sp, y, Comma, Sp, row, Sp, Le, Sp, Call("RowFixedMass", h, p, y), Close,
            Sp, Land, Sp, Call("UniversalFixedMassBound", h, p, row),
            Sp, Land, Sp, Call("PositiveInvariantAttainment", h, p, row)));
    }
}
