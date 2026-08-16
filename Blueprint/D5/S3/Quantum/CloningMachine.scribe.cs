using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class CloningMachineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universal symmetric cloning machine has an input-independent machine entropy.",
        H("Cloning Machine Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cloning-machine-entropy-has-an-exact-closed-form"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/CloningMachine.machine_entropy_closed_form"),
                H("The cloning machine entropy has an exact closed form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("machineEntropy")), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("logb")), Open,
                    D(2), Comma, Sp, D(3), Close,
                    Sp, Minus, Sp, Frac, Grp(D(2)), Grp(D(3))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen module first derives that every normalized pure qubit input "
                        + "gives the universal symmetric 1-to-2 cloning machine a reduced-state "
                        + "spectrum of {1/3, 2/3}. The definition machineEntropy packages the "
                        + "binary entropy of those eigenvalues, so it is independent of the input.")),
                    Paragraph(Text(
                        "Expanding that definition and applying the real logarithm quotient laws "
                        + "gives the exact value logb(2, 3) - 2/3 bits. This declaration proves "
                        + "the closed-form entropy identity only; it does not construct the cloning "
                        + "isometry or strengthen the universal no-cloning theorem."))),
                DescribeRole.Theorem))));
}
