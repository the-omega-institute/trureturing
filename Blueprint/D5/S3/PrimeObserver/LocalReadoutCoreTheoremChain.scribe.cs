using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver;

internal sealed class LocalReadoutCoreTheoremChainDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/PrimeObserver/LocalReadoutCoreTheoremChain."
            + "local_readout_core_theorem_chain";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint kernels, finite certificates, and CRT phase periods form one theorem chain.",
        H("The Local-Readout Core Theorem Chain"),
        Blocks(Describe.Lean(
            DescribeId.Create("local-readout-core-theorem-chain"),
            DeclarationHandle.Create(Declaration),
            H("Separation, certification, and crossing periods"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Joint injectivity, point separation, and diagonal kernel intersection "
                        + "are equivalent, and residual emptiness is the same condition.")),
                Paragraph(Text(
                    "A finite operational quotient admits a finite distinguishing "
                        + "certificate even when the available protocol family is infinite.")),
                Paragraph(Text(
                    "For a nonzero modulus the crossing phase period is the least common "
                        + "multiple of its prime-power periods; zero is an explicit "
                        + "counterexample, while the sandwich phase first returns at six."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        F.Id("JointFaithfulnessTFAE"),
        Sp, Land, Sp,
        Grp(F.Id("LGResEmpty"), Sp, Iff, Sp, F.Id("JointInjective")),
        Sp, Land, Sp,
        F.Id("FiniteCertificate"),
        Sp, Land, Sp,
        Grp(F.Id("m"), Sp, Neq, Sp, Num(0), Sp, Implies, Sp,
            F.Id("T(m)"), Sp, Eq, Sp, F.Id("lcmPrimePowerPeriods")),
        Sp, Land, Sp,
        F.Id("ZeroModulusCounterexample"),
        Sp, Land, Sp,
        F.Id("FirstReturnSix"), Dot));
}
