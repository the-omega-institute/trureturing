using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Solenoid;

internal sealed class AllPrimeRegisterExactSequenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-prime register is exact with a prime-adic hidden kernel.",
        H("All-Prime Register Exact Sequence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-prime-register-short-exact-sequence"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Solenoid/AllPrimeRegisterExactSequence."
                    + "all_prime_register_short_exact"),
                H("The all-prime register has the full prime-adic kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Sp, To, Sp,
                    Prod, Underscore, Grp(F.Id("p"), Sp, F.Text, Grp(F.Id("prime"))),
                    Sp, Mathbb, Grp(F.Id("Z")), Underscore, Grp(F.Id("p")),
                    Sp, To, Sp, Sigma, Sp, To, Sp,
                    Mathbb, Grp(F.Id("T")), Sp, To, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the register containing every prime. Its hidden fiber is the "
                        + "product of one prime-adic integer ring for each prime, and its visible "
                        + "coordinate is a point on the circle. The theorem states injectivity "
                        + "of the hidden-fiber inclusion, exactness at the universal solenoid, "
                        + "surjectivity of the visible projection, and bijectivity of the kernel "
                        + "classification.")),
                    Paragraph(Text(
                        "This is the source-enumerated all-prime exact-sequence clause. It does "
                        + "not assert an arbitrary-prime-set construction or identify the "
                        + "universal solenoid with a separately defined rational dual.")),
                    Paragraph(Text(
                        "The repository already proves the exactness, surjectivity, and kernel "
                        + "classification in universal_solenoid_profinite_exact. The present "
                        + "theorem applies that exact result and records the injectivity of the "
                        + "canonical subtype inclusion explicitly."))),
                DescribeRole.Theorem))));
}
