using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.NoisyMemory;

internal sealed class ParityResolventChordDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/chen2026noisyquantummemory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quadratic inverse has a sharp squared-attenuation upper chord.",
        H("Quadratic inverses under parity attenuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("squared-attenuation-chord"),
                DeclarationHandle.Create(Module + "sSup_trialValue_chord"),
                H("Upper chord with squared attenuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Scale the odd source and the even–odd coupling by the same real factor a in [0,1]. "
                    + "After scaling the odd trial vector by a, the objective is affine in a². "
                    + "Its supremum is bounded by the fully pinched and unattenuated endpoint values "
                    + "with weights 1 − a² and a²."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-supremum-linear-solution"),
                DeclarationHandle.Create(Module + "variationalValue_eq_inner_of_solve"),
                H("The variational optimum at a linear solution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a symmetric nonnegative quadratic form with operator A, any solution "
                    + "Aw = r attains the supremum of the trial objective. Completing the square "
                    + "identifies the optimum with the inner product of w and r."))),
                DescribeRole.Theorem))));
}
