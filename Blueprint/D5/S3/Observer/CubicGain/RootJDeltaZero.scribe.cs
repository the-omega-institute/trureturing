using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class RootJDeltaZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Root J history coordinates under zero Delta",
        H("Zero Delta history coordinates on the whole native kernel"),
        Blocks(
            Paragraph(Text("For every complete assignment of the 256 original source matrices, the Lean carrier keeps the original 1538 by 1024 comparison map: each of the 254 nonempty chronological prefixes compares every nonreference descendant with the first descendant, and V is its full kernel. A coefficient block is the complete four coefficient vector, including its constant coefficient; zero blocks remain in the kernel domain.")),
            Paragraph(Text("The theorem delta_zero_history_coordinates assumes Delta is zero as a linear form on this whole V. For every x in V it derives the native history identities F(x)=5*x(0,2)+60*x(0,3), E(x)=8*x(0,2)+72*x(0,3), history(5)(x)=F(x), history(6)(x)=2*F(x)+E(x)/4, and history(7)(x)=21*F(x)/5. These are consequences of the original chronological acquisition and preserve the four coefficient coordinates.")),
            Describe.Lean(
                DescribeId.Create("root-j-delta-zero-history-coordinates"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/RootJDeltaZero.delta_zero_history_coordinates"),
                H("The zero Delta coordinate identities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original source assignment P, every x in the full native kernel V P, and Delta P=0, the five displayed linear identities hold. The source assignment is unrestricted beyond the original legal-source predicate used by the native acquisition carrier."))),
                DescribeRole.Theorem))));
}
