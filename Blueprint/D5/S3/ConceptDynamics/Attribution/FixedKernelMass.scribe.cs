using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class FixedKernelMassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/FixedKernelMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp mass of globally fixed seeds in equivariant probability calibration.",
        H("Maximum mass of globally fixed seeds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-fixed-seed-mass"),
                DeclarationHandle.Create(Prefix + "maximal_fixed_seed_mass"),
                H("The least row mass on stabilizer-fixed outputs is attained"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A group G acts on a nonempty finite input set X and a finite output set Y. "
                        + "The nonnegative kernel P has row sums one and is covariant. RowFixedMass "
                        + "sums a row over the outputs fixed by every group element fixing that input. "
                        + "SeedFixedMass sums the weights of all seeds fixed by the whole group.")),
                    Paragraph(Text(
                        "The same minimizing row bounds the fixed mass of every finite calibration "
                        + "with nonnegative weights and an equivariant readout. There is an attaining "
                        + "calibration with strictly positive weights summing to one, invariant under "
                        + "the group action, with all row marginals equal to P.")),
                    Paragraph(Text(
                        "For attainment, take the least row mass in proportion from each row's "
                        + "stabilizer-fixed output set. Sample the normalized fixed part at one "
                        + "representative per input orbit and transport the outputs along the orbit. "
                        + "The residual kernel is calibrated by independent row draws. Mix the two "
                        + "parts using their total masses and omit the part of weight zero at each endpoint."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula p = F.Id("P");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula row = Call("RowFixedMass", p, x);
        return Disp(Seq(Forall, Sp, p, Comma, Sp, Call("CovariantProbabilityKernel", p),
            Sp, Rightarrow, Sp, Exists, Sp, x, Comma, Sp,
            Open, Forall, Sp, y, Comma, Sp, row, Sp, Le, Sp, Call("RowFixedMass", p, y), Close,
            Sp, Land, Sp, Call("UniversalFixedMassBound", p, row),
            Sp, Land, Sp, Call("PositiveInvariantAttainment", p, row)));
    }
}
