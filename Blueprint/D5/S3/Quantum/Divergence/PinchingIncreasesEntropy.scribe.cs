using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class PinchingIncreasesEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Basis pinching increases von Neumann entropy whenever its relative-entropy gain "
            + "has an explicit nonnegativity certificate.",
        H("Entropy Increase Under Basis Pinching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-density-states-have-nonnegative-relative-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/PinchingIncreasesEntropy."
                        + "quantum_relative_entropy_nonnegative_unit"),
                H("Relative entropy is nonnegative in dimension one"),
                StatementSource.FromAuthor(UnitNonnegativityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A density state on the one-point carrier has a single matrix entry, "
                            + "and the trace-one condition forces that entry to be one. Hence "
                            + "both states are the unique one-dimensional density state.")),
                    Paragraph(Text(
                        "Their quantum relative entropy is therefore zero, which supplies the "
                            + "nonnegativity certificate in dimension one. This does not prove "
                            + "relative-entropy nonnegativity in higher dimensions."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("pinching-entropy-gain-equals-relative-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/PinchingIncreasesEntropy."
                        + "pinching_entropy_gain_eq_relative_entropy"),
                H("Pinching entropy gain is relative entropy"),
                StatementSource.FromAuthor(PinchingGainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a complete rank-one record measurement send rho to sigma, with "
                            + "the logarithm of sigma lying in the measurement's diagonal "
                            + "Hermitian subspace. The entropy gained from replacing rho by "
                            + "sigma is exactly their quantum relative entropy.")),
                    Paragraph(Text(
                        "The preceding pinching identity expresses the entropy of sigma as the "
                            + "entropy of rho plus relative entropy. Subtracting the entropy of "
                            + "rho gives the stated gain identity."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("basis-pinching-increases-von-neumann-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/PinchingIncreasesEntropy."
                        + "pinching_increases_entropy"),
                H("Basis pinching cannot decrease von Neumann entropy"),
                StatementSource.FromAuthor(PinchingMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same basis-pinching and diagonal-logarithm conditions, an "
                            + "explicit certificate that the relative entropy of rho from sigma "
                            + "is nonnegative makes the entropy of sigma at least that of rho.")),
                    Paragraph(Text(
                        "The exact gain identity identifies the entropy difference with the "
                            + "certified nonnegative relative entropy. Thus monotonicity follows "
                            + "without any further matrix inequality.")),
                    Paragraph(Text(
                        "The certificate is an assumption in arbitrary positive dimension; this "
                            + "module proves it only for the one-dimensional carrier. The result "
                            + "does not establish the general Klein inequality, Schur--Horn "
                            + "pinching, or Heisenberg-side capacity monotonicity."))),
                DescribeRole.Theorem))));

    private static Formula UnitNonnegativityFormula()
    {
        Formula densityState = Call("DensityState", F.Id("Unit"));

        return Disp(Seq(
            Forall, Sp, Rho, Comma, Sp, SigmaLower, Colon, Sp, densityState, Comma, Sp,
            D(0), Sp, Leq, Sp,
            Call("quantumRelativeEntropy", Rho, SigmaLower), Dot));
    }

    private static Formula PinchingGainFormula()
    {
        Formula dimension = F.Id("d");
        Formula basis = F.Id("B");
        Formula densityState = Call("DensityState", dimension);
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));
        Formula pinchedState = Call("basisMeasurement", basis, Rho);
        Formula diagonalSubspace = Call("diagonalSubspace", basis);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, dimension, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", dimension), Comma, Sp,
            Rho, Comma, Sp, SigmaLower, Colon, Sp, densityState, Comma, RowBreak, Grp(),
            dimension, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            recordMeasurement, Sp, Land, Sp,
            pinchedState, Sp, Eq, Sp, SigmaLower, Sp, Land, RowBreak, Grp(),
            Call("log", SigmaLower), Sp, InMacro, Sp, diagonalSubspace,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("entropyGain", Rho, SigmaLower), Sp, Eq, Sp,
            Call("quantumRelativeEntropy", Rho, SigmaLower), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula PinchingMonotonicityFormula()
    {
        Formula dimension = F.Id("d");
        Formula basis = F.Id("B");
        Formula densityState = Call("DensityState", dimension);
        Formula recordMeasurement = Call("IsRecordMeasurement", Call("projector", basis));
        Formula pinchedState = Call("basisMeasurement", basis, Rho);
        Formula diagonalSubspace = Call("diagonalSubspace", basis);
        Formula relativeEntropy = Call("quantumRelativeEntropy", Rho, SigmaLower);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, dimension, Comma, Sp,
            basis, Colon, Sp, Call("RankOneContext", dimension), Comma, Sp,
            Rho, Comma, Sp, SigmaLower, Colon, Sp, densityState, Comma, RowBreak, Grp(),
            dimension, Sp, Geq, Sp, D(1), Sp, Land, Sp,
            recordMeasurement, Sp, Land, Sp,
            pinchedState, Sp, Eq, Sp, SigmaLower, Sp, Land, RowBreak, Grp(),
            Call("log", SigmaLower), Sp, InMacro, Sp, diagonalSubspace, Sp, Land, Sp,
            D(0), Sp, Leq, Sp, relativeEntropy, Sp, Rightarrow, RowBreak, Grp(),
            Call("vonNeumannEntropy", Rho), Sp, Leq, Sp,
            Call("vonNeumannEntropy", SigmaLower), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
