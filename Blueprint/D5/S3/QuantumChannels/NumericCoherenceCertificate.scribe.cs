using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class NumericCoherenceCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactly two hundred phase-damping channels preserve classical zero coherence while a biased diagonal witness has Hadamard coherence seven fiftieth.",
        H("Two-Hundred-Channel Numeric Coherence Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("biased-diagonal-density-is-the-explicit-state-witness"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/NumericCoherenceCertificate.biasedDiagonalDensity"),
                H("The biased diagonal density is the explicit state witness"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("rho"), Eq, Operatorname, Grp(F.Id("diag")), Open,
                    Frac, Grp(D(1, 6)), Grp(D(2, 5)), Comma, Frac, Grp(D(9)), Grp(D(2, 5)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The witness is the non-maximally-mixed diagonal matrix diag(16/25, 9/25). Its entries are nonnegative, its trace is one, and its standard-basis off-diagonal pair is exactly zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("apply-channel-family-folds-fin-two-hundred"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/NumericCoherenceCertificate.applyChannelFamily"),
                H("The channel family is a finite fold over Fin 200"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("A"), Open, F.Id("c"), Close, Open, Rho, Close, Eq,
                    Operatorname, Grp(F.Id("fold")), Open, F.Id("c"), Comma, Rho, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every coefficient function c : Fin 200 -> DampingCoefficient, the definition folds exactly 200 existing phaseDamping operations over the evolving qubit matrix. The finite list is object-level and is not replaced by an iterate shorthand."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("the-biased-diagonal-density-is-a-state"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/NumericCoherenceCertificate.biased_diagonal_density_is_state"),
                H("The biased diagonal density is positive and normalized"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("trace")), Open, Rho, Close, Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Entrywise positivity and exact finite trace arithmetic establish the density-state obligations for the witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-hundred-phase-damping-channels-preserve-zero-coherence"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_channel_zero_coherence"),
                H("Two hundred phase-damping channels preserve zero coherence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), Colon, Sp, Operatorname, Grp(F.Id("Fin")), Open, D(2, 0, 0), Close,
                    Sp, To, Sp, Operatorname, Grp(F.Id("Damping")), Comma, Esc,
                    Operatorname, Grp(F.Id("offDiag")), Open, Rho, Close, Eq, D(0), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("offDiag")), Open,
                    Operatorname, Grp(F.Id("applyChannelFamily")), Open, F.Id("c"), Comma, Rho, Close, Close, Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-step entrywise lemma shows that phaseDamping cannot create either off-diagonal entry from zero. List induction then proves the invariant for the complete Fin 200 fold, for every coefficient family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-hadamard-witness-has-exact-seven-fiftieth-coherence"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/NumericCoherenceCertificate.biased_diagonal_hadamard_certificate"),
                H("The Hadamard witness has exact seven-fiftieth coherence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("offDiag")), Open,
                    Operatorname, Grp(F.Id("hadamardCoordinates")), Open, Rho, Close, Close, Eq,
                    Open, Frac, Grp(D(7)), Grp(D(5, 0)), Comma, Frac, Grp(D(7)), Grp(D(5, 0)), Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("offDiag")), Open,
                    Operatorname, Grp(F.Id("hadamardCoordinates")), Open, Rho, Close, Close, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit Hadamard coordinate formula computes both coherence entries as 7/50, which is 0.14, and norm_num proves this pair is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-concrete-nonidentity-two-hundred-family-is-inhabited"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_nonidentity_family_witness"),
                H("A concrete nonidentity two-hundred-channel family inhabits the certificate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("c"), InMacro, Sp, Operatorname, Grp(F.Id("Fin")), Open, D(2, 0, 0), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("offDiag")), Open,
                    Operatorname, Grp(F.Id("applyChannelFamily")), Open, F.Id("c"), Comma, Rho, Close, Close, Eq, D(0), Sp,
                    Land, Sp, Exists, Sp, F.Id("i"), Comma, Esc, Open, F.Id("c"), Close, Neq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Taking every one of the 200 coefficients to be 1/2 supplies an inhabited, genuinely nonidentity family. The same fold proof gives zero output coherence for this concrete family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complete-two-hundred-channel-and-hadamard-certificate"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/NumericCoherenceCertificate.two_hundred_classical_channels_and_hadamard_certificate"),
                H("The complete two-hundred-channel and Hadamard certificate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), Colon, Sp, Operatorname, Grp(F.Id("Fin")), Open, D(2, 0, 0), Close,
                    Sp, To, Sp, Operatorname, Grp(F.Id("Damping")), Comma, Esc,
                    Operatorname, Grp(F.Id("offDiag")), Open, Rho, Close, Eq, D(0), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("offDiag")), Open, Operatorname, Grp(F.Id("applyChannelFamily")), Open, F.Id("c"), Comma, Rho, Close, Close, Eq, D(0), Sp,
                    Land, Sp, Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("trace")), Open, Rho, Close, Eq, D(1), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("offDiag")), Open, Operatorname, Grp(F.Id("hadamardCoordinates")), Open, Rho, Close, Close, Eq,
                    Open, Frac, Grp(D(7)), Grp(D(5, 0)), Comma, Frac, Grp(D(7)), Grp(D(5, 0)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This theorem packages the exact finite certificate: all 200 object-level classical channels preserve zero standard-basis coherence, while the same physical witness has the exact nonzero Hadamard pair (7/50, 7/50)."))),
                DescribeRole.Theorem))));
}
