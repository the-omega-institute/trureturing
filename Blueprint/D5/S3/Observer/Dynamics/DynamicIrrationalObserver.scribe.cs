using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class DynamicIrrationalObserverDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Dynamics/DynamicIrrationalObserver.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dynamic irrational observer has a contractive ratio and an infinite higher jet.",
        H("Dynamic Irrational Observer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dynamic-irrational-observer"),
                DeclarationHandle.Create(DeclarationPrefix + "Observer"),
                H("Contractive observer with an infinite jet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observer records a completed value, a contraction ratio, a linear "
                            + "coefficient, and a genuinely infinite family of higher coefficients "
                            + "indexed directly by every natural number from two onward.")),
                    Paragraph(Text(
                        "A thread realizes these data when the higher-order terms have the stated "
                            + "infinite sum at every time. This explicit HasSum relation does not "
                            + "silently assign a real value to a non-summable formal series.")),
                    Paragraph(Text(
                        "The zeroth readout is the completed value, the first readout is the linear "
                            + "coefficient, and every readout from order two is the corresponding "
                            + "higher coefficient.")),
                    Paragraph(Text(
                        "The golden first observation class is inhabited. Its completed value is "
                            + "the golden ratio, its contraction is minus the inverse golden ratio "
                            + "squared, its linear coefficient is one, and all higher coefficients "
                            + "vanish; the thread is the golden ratio plus the nth power of the "
                            + "contraction.")),
                    Paragraph(Text(
                        "The source's full-jet reconstruction sentence is not asserted as "
                            + "injectivity: the displayed readout sequence omits the contraction "
                            + "ratio, and the source gives no convergence condition for arbitrary "
                            + "higher coefficients."))),
                DescribeRole.Definition))));
}
