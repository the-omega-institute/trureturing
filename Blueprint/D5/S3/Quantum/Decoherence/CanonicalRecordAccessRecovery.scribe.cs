using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class CanonicalRecordAccessRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reversible coupling preserves phase information in the canonical environment record "
            + "even when that information is unavailable from the reduced state.",
        H("Canonical Record Access Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-record-exposes-a-reduced-access-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery."
                        + "reduced_irreversibility_is_canonical_record_access_defect"),
                H("Reduced irreversibility is a canonical record access defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho and sigma be system matrices with the same populations and a "
                            + "different off-diagonal coherence. The controlled-copy permutation "
                            + "writes each input into the canonical copied-address environment "
                            + "record.")),
                    Paragraph(Text(
                        "The permutation matrix is unitary and produces both joint record states. "
                            + "Those states remain distinct, but tracing the environment makes "
                            + "their reduced system states equal, so no one function of the "
                            + "reduced state can reconstruct both joint records.")),
                    Paragraph(Text(
                        "Applying the adjoint global coupling to either canonical joint record "
                            + "restores its original blank-record input exactly. Global reversible "
                            + "generation therefore does not imply local engineering recovery when "
                            + "the phase-bearing record is outside the available control domain."))),
                DescribeRole.Theorem))));

    private static Formula Entry(Formula matrix, Formula i, Formula j) =>
        Seq(matrix, Underscore, Grp(i, j));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula rho = Rho;
        Formula sigma = SigmaLower;
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula unitary = F.Id("U");
        Formula matrixType = Seq(Operatorname, Grp(F.Id("QubitMatrix")));
        Formula jointType = Seq(Operatorname, Grp(F.Id("JointQubitEnvironmentMatrix")));
        Formula recordRho = Call("canonicalRecord", rho);
        Formula recordSigma = Call("canonicalRecord", sigma);
        Formula blankRho = Call("blank", rho);
        Formula blankSigma = Call("blank", sigma);
        Formula traceRho = Call("traceEnvironment", recordRho);
        Formula traceSigma = Call("traceEnvironment", recordSigma);
        Formula forwardRho = Call("evolve", unitary, blankRho);
        Formula forwardSigma = Call("evolve", unitary, blankSigma);
        Formula adjoint = Seq(unitary, Caret, Grp(Star));
        Formula reverseRho = Call("evolve", adjoint, recordRho);
        Formula reverseSigma = Call("evolve", adjoint, recordSigma);
        Formula recover = F.Id("recover");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, rho, Comma, Sp, sigma, Colon, Sp, matrixType, Comma, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp, Entry(rho, i, i), Sp, Eq, Sp,
                Entry(sigma, i, i), Close, Sp, Land, RowBreak, Grp(),
            Open, Exists, Sp, i, Comma, Sp, j, Comma, Sp, i, Sp, Neq, Sp, j,
                Sp, Land, Sp, Entry(rho, i, j), Sp, Neq, Sp, Entry(sigma, i, j), Close,
                Sp, Rightarrow, RowBreak, Grp(),
            Call("Unitary", unitary), Sp, Land, RowBreak, Grp(),
            forwardRho, Sp, Eq, Sp, recordRho, Sp, Land, RowBreak, Grp(),
            forwardSigma, Sp, Eq, Sp, recordSigma, Sp, Land, RowBreak, Grp(),
            traceRho, Sp, Eq, Sp, traceSigma, Sp, Land, RowBreak, Grp(),
            recordRho, Sp, Neq, Sp, recordSigma, Sp, Land, RowBreak, Grp(),
            Open, Neg, Exists, Sp, recover, Colon, Sp,
                new Formula.TypeArrow(matrixType, jointType), Comma, RowBreak, Grp(),
            Open, At(recover, traceRho), Sp, Eq, Sp, recordRho, Sp, Land, RowBreak, Grp(),
                At(recover, traceSigma), Sp, Eq, Sp, recordSigma, Close, Close,
                Sp, Land, RowBreak, Grp(),
            reverseRho, Sp, Eq, Sp, blankRho, Sp, Land, RowBreak, Grp(),
            reverseSigma, Sp, Eq, Sp, blankSigma, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
