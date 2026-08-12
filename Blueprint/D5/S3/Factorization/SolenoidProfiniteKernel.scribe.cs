using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class SolenoidProfiniteKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universal solenoid projects exactly onto the circle with all-prime profinite kernel.",
        H("The Hidden Fiber of the Universal Solenoid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("universal-solenoid-profinite-exact-sequence"),
                DeclarationHandle.Create("D5/S3/Factorization/SolenoidProfiniteKernel.universal_solenoid_profinite_exact"),
                H("The visible circle projection has the all-prime profinite kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                                    D(0), Sp, To, Sp,
                                    Prod, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(F.Id("prime"))),
                                    Sp, Mathbb, Grp(F.Id("Z")), Underscore, Grp(F.Id("p")),
                                    Sp, To, Sp, Sigma, Sp, To, Sp,
                                    Mathbb, Grp(F.Id("T")), Sp, To, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The universal solenoid is the compatible family of circle phases "
                                        + "indexed by all positive moduli. Evaluation at modulus one is "
                                        + "surjective onto the visible circle. The theorem proves exactness "
                                        + "at the solenoid and identifies the full kernel bijectively with "
                                        + "one prime-adic integer coordinate for every prime. Thus every "
                                        + "kernel point is present in the displayed product exactly once.")),
                                    Paragraph(Text(
                                        "This is new assembly over pinned Mathlib rather than a wrapper around "
                                        + "an existing solenoid theorem. A compatible residue modulo each "
                                        + "positive integer maps to a compatible circle coordinate. Conversely, "
                                        + "a kernel point has an m-torsion coordinate at every modulus m; the "
                                        + "finite-torsion classification of the circle recovers its unique "
                                        + "residue. Compatibility follows from the solenoid relation and "
                                        + "injectivity of the residue embedding into the circle. The resulting "
                                        + "residue equivalence is composed with the deposited prime-adic "
                                        + "decomposition. The source atom contains no numerical certificate."))),
                DescribeRole.Theorem
            ))));
}
