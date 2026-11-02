using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class TwoPathConcentrationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact signed-Catalan shift-three series law for two odd path factors, with an arbitrary residual factor.",
        H("Two odd paths: the signed-Catalan shift-three series law"),
        Blocks(
            Describe.Lean(DescribeId.Create("series-law"),
                DeclarationHandle.Create(Prefix + "two_path_series_concentration"),
                H("The reusable two-path series identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For p and q at least one, the actual independent-set partition series of paths of orders 2p+1 and 2q+1, after multiplication by any residual series and the integer Catalan series, differs from the order 2p+2q+1 path with one isolated vertex by X cubed times the two path tails of orders 2p-2 and 2q-2.")),
                    Paragraph(Text("The proof uses the actual independent-configuration deletion recurrence on the natural-number Hasse path, the Catalan functional equation, and strong induction on the sum of the two path orders. The residual series is arbitrary and is carried through by multiplication.")),
                    Paragraph(Text("A transient coefficient check compiles the exact natural-subtraction shift at every legal m. Faithful transport from an arbitrary same-carrier labelled graph to this series factorization is an integration obligation for the next delivery."))),
                DescribeRole.Theorem)), []));
}
