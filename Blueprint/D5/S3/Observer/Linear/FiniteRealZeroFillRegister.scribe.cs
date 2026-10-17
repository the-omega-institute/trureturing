using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class FiniteRealZeroFillRegisterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Linear/FiniteRealZeroFillRegister.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite real zero-fill register reads every original sign through its horizon.",
        H("Finite Real Zero-Fill Register"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-x"),
                DeclarationHandle.Create(Prefix + "X"),
                H("Infinite binary inputs"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An input is an arbitrary function from natural times to Bool; no finite encoding or probability measure is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-bitsign"),
                DeclarationHandle.Create(Prefix + "bitSign"),
                H("The original real sign"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original sign is minus one raised to the Boolean natural value: false has sign +1 and true has sign -1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-signal"),
                DeclarationHandle.Create(Prefix + "signal"),
                H("The time-indexed original signal"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At time t the signal reads the sign of the original input coordinate x(t)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-state"),
                DeclarationHandle.Create(Prefix + "State"),
                H("The finite real state"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any natural horizon H, the state is the real vector with coordinates Fin(H+1). Its entries are arbitrary real numbers; H=0 still has coordinate zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-initstate"),
                DeclarationHandle.Create(Prefix + "initState"),
                H("Initialization from the original input"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Initialize coordinate i with signal(i,x), thereby storing the first H+1 original signs once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-update"),
                DeclarationHandle.Create(Prefix + "update"),
                H("A fixed linear update with real-zero fill"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The update copies coordinate i+1 when that coordinate lies in Fin(H+1), and otherwise writes the real number 0. Both additivity and real scalar compatibility are part of this linear map. The boundary value is different from the sign of false. The update uses neither time nor a subsequent input sample."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-readout"),
                DeclarationHandle.Create(Prefix + "readout"),
                H("A fixed linear readout"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The readout is the real-linear coordinate-zero projection on the same finite real state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-update-iterate"),
                DeclarationHandle.Create(Prefix + "update_iterate"),
                H("Every in-bound coordinate of every iterate"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all H,t, arbitrary real state q and coordinate i satisfying i.val+t<H+1, the t-fold update at i equals the original q at i.val+t. Induction on t applies the successor equation for function iteration; the in-bound inequality selects the copy branch at the successor step. The statement concerns only in-bound coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-real-zero-fill-pointwise-attainment"),
                DeclarationHandle.Create(Prefix + "pointwise_attainment"),
                H("Pointwise attainment of the original signal"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the arbitrary-state invariant to the initialized vector at coordinate zero. For every infinite input x and every t<=H, including H=t=0, the fixed readout after t fixed updates is exactly signal(t,x). This is the finite real construction in original theorem 12.4. In the binary-shift source, the unit-word orbit at coordinate j is x(j+word.length); its coordinate-zero sign observation is therefore this same signal at time t. The construction proves the pointwise upper realization. It asserts no lower bound, minimum dimension, state cardinality, after-boundary identity, or almost-everywhere endpoint."))),
                DescribeRole.Theorem))));
}
