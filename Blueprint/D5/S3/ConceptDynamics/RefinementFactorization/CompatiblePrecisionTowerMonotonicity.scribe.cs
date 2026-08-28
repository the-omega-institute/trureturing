using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class CompatiblePrecisionTowerMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent levels of a compatible prime-indexed precision tower are ordered "
            + "by refinement, with equality kernels ordered in reverse.",
        H("Compatible Precision Tower Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compatible-precision-towers-refine-monotonically"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementFactorization/"
                        + "CompatiblePrecisionTowerMonotonicity."
                        + "compatible_precision_tower_monotonicity"),
                H("Compatible adjacent precision levels refine monotonically"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p range over prime natural numbers. At every precision k, the "
                            + "readout q maps states into its level-dependent output type. "
                            + "A lowering map from level k + 1 to level k is required to "
                            + "recover the coarser readout exactly.")),
                    Paragraph(Text(
                        "That lowering map is the canonical factor witnessing refinement. "
                            + "The repository's relative-identity refinement theorem then "
                            + "applies the same compatibility equation to contain the finer "
                            + "equality kernel in the coarser one.")),
                    Paragraph(Text(
                        "Both clauses of theorem 7.1 are public: adjacent readout refinement "
                            + "and reverse inclusion of their equality kernels. No claim about "
                            + "the inverse limit or independence between levels is included."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula MonotonicityFormula()
    {
        Formula prime = F.Id("p");
        Formula level = F.Id("k");
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula lower = F.Id("rho");
        Formula nextLevel = Seq(level, Plus, D(1));
        Formula currentIndex = Seq(prime, Comma, level);
        Formula nextIndex = Seq(prime, Comma, nextLevel);
        Formula currentOutput = Subscript(output, currentIndex);
        Formula nextOutput = Subscript(output, nextIndex);
        Formula currentReadout = Subscript(readout, currentIndex);
        Formula nextReadout = Subscript(readout, nextIndex);
        Formula lowering = Subscript(lower, Seq(prime, Comma, nextLevel, Comma, level));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula primes = Call("NatPrime", prime);

        return Disp(Seq(
            Forall, Sp, state, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            output, Colon, Sp,
            Open, prime, Colon, Sp, naturals, Comma, Sp, primes, Close,
            Sp, To, Sp, naturals, Sp, To, Sp, type, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, Forall, Sp,
            prime, Colon, Sp, naturals, Comma, Sp, primes, Comma, Sp,
            level, Colon, Sp, naturals, Comma, Sp,
            state, Sp, To, Sp, currentOutput, Comma,
            RowBreak, Grp(),
            lower, Colon, Sp, Forall, Sp,
            prime, Colon, Sp, naturals, Comma, Sp, primes, Comma, Sp,
            level, Colon, Sp, naturals, Comma, Sp,
            nextOutput, Sp, To, Sp, currentOutput, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, prime, Comma, Sp, level, Comma, Sp,
            currentReadout, Sp, Eq, Sp,
            lowering, Sp, Circ, Sp, nextReadout, Close,
            Sp, Rightarrow, Sp,
            Forall, Sp, prime, Colon, Sp, naturals, Comma, Sp, primes, Comma, Sp,
            level, Colon, Sp, naturals, Comma,
            RowBreak, Grp(),
            Call("Refines", currentReadout, nextReadout), Sp, Land, Sp,
            Call("ker", nextReadout), Sp, Subseteq, Sp,
            Call("ker", currentReadout), Dot));
    }
}
