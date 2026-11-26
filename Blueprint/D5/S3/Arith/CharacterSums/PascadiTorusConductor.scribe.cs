using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiTorusConductorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/CharacterSums/PascadiTorusConductor.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic torus reduction and the cubic character decomposition for a prime-cube word.",
        H("Cayley transform and reduction of the norm-one group"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-torus-cayley-word"),
                DeclarationHandle.Create(Module + "cayley_word_eq_one_iff"),
                H("The cubic word as a product in the norm-one group"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("In the quadratic algebra with t squared equal to minus d, the Cayley transform sends x to (1+t*x)/(1-t*x) whenever 1+d*x squared is a unit. The transform has norm one.")),
                    Paragraph(Text("When 2 is invertible, the product of three transforms is one exactly when x+y+z=d*x*y*z. Clearing the three unit denominators reduces the equality to the imaginary coordinate of the difference of the two products."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-torus-reduction-kernel"),
                DeclarationHandle.Create(Module + "primeCube_unitary_card_ker"),
                H("The kernel has order p"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For odd prime p the reduction from the quadratic norm-one group over Z/p cubed to the one over Z/p squared is onto. A lift is corrected by a scalar equal to one minus half its norm defect. The defect lies in the square-zero ideal.")),
                    Paragraph(Text("In trace-zero coordinates the kernel consists of 1+t*b with b in the additive reduction kernel. Multiplication of these elements adds their b coordinates. The base ring reduction has kernel size p."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-torus-cubic-conductor-split"),
                DeclarationHandle.Create(Module + "primeCube_wordMass_conductor_split"),
                H("The exact prime-cube character decomposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("With an arbitrary weight on the prime-cube norm-one group, the product-one mass of ordered triples equals the corresponding mass after reduction divided by p, plus the normalized difference of the two cubic character sums.")),
                    Paragraph(Text("Finite abelian character orthogonality gives each of the two cubic moments. Surjective reduction identifies the characters factoring through the square modulus with the pulled-back character family. The signed primitive moment in this identity remains the analytic estimation problem in the six-return application."))),
                DescribeRole.Theorem))));
}
