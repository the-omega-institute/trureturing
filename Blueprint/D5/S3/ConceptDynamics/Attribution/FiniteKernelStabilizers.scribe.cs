using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class FiniteKernelStabilizersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stabilizers of positive seeds for finite covariant probability kernels.",
        H("Supported fixed outputs and calibrating seeds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-kernel-seed-stabilizer"),
                DeclarationHandle.Create(Prefix + "stabilizer_possible_iff"),
                H("A specified subgroup can fix a positive seed"),
                StatementSource.FromAuthor(Statement("HasSeedFixedBy")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A group G acts on a finite input set X and a finite output set Y. "
                        + "P is a nonnegative real kernel, each row sums to one, and "
                        + "P evaluated at g acting on x and y equals P at x and y. "
                        + "H is a subgroup of G.")),
                    Paragraph(Text(
                        "HasSeedFixedBy means there is a finite G-set of seeds with positive "
                        + "invariant real weights summing to one and a covariant deterministic "
                        + "readout on inputs and seeds. The mass of seeds sent to y at x is "
                        + "P(x,y). Some seed is fixed by every element of H. "
                        + "SupportedFixedOutputs means that for every x, there is a y of "
                        + "positive row mass fixed by every element of H fixing x.")),
                    Paragraph(Text(
                        "A fixed seed yields a supported output by positivity and covariance. "
                        + "For the converse, choose a supported fixed output at one representative "
                        + "of each H-orbit of inputs and transport it over that orbit. This produces "
                        + "an H-equivariant table. On all tables choosing positive entries, assign "
                        + "each table the product of its row probabilities. Relabeling both the "
                        + "inputs and the outputs preserves the product. Finite product "
                        + "distributivity gives each required marginal. The chosen table has "
                        + "positive mass and is fixed by H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-kernel-exact-seed-stabilizer"),
                DeclarationHandle.Create(Prefix + "exact_stabilizer_possible_iff"),
                H("A prescribed subgroup can be the full stabilizer"),
                StatementSource.FromAuthor(ExactStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the same kernel assumptions. HasSeedWithStabilizer asks for a seed "
                        + "whose full stabilizer is H. Its orbit is in bijection with the left "
                        + "coset space of H, which must therefore be finite.")),
                    Paragraph(Text(
                        "Start with a seed fixed by H. Enlarge the seed space by an independent "
                        + "uniform left coset. Ignore that coordinate when reading the output. "
                        + "The product action preserves this law and the marginal masses. "
                        + "At the original seed paired with the identity coset, the stabilizer "
                        + "is the intersection of the original stabilizer with H, hence H."))),
                DescribeRole.Theorem))));

    private static Formula Statement(string name)
    {
        var p = F.Id("P");
        var h = F.Id("H");
        return Disp(Seq(Call("CovariantKernel", p), Sp, Rightarrow, Sp,
            Open, Call(name, p, h), Sp, Iff, Sp, Call("SupportedFixedOutputs", p, h), Close));
    }

    private static Formula ExactStatement()
    {
        var p = F.Id("P");
        var h = F.Id("H");
        return Disp(Seq(Call("CovariantKernel", p), Sp, Rightarrow, Sp,
            Open, Call("HasSeedWithStabilizer", p, h), Sp, Iff, Sp,
            Open, Call("FiniteIndex", h), Sp, Land, Sp, Call("SupportedFixedOutputs", p, h),
            Close, Close));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
