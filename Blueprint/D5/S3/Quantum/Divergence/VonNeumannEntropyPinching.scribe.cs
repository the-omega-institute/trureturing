using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class VonNeumannEntropyPinchingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Von Neumann entropy is compatible with quantum relative entropy, and basis "
            + "pinching has an exact entropy gain when the target logarithm is diagonal.",
        H("Von Neumann Entropy Under Basis Pinching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "quantum-relative-entropy-splits-into-entropy-and-cross-term"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/VonNeumannEntropyPinching."
                        + "quantum_relative_entropy_eq_neg_entropy_sub_cross"),
                H("Quantum relative entropy splits into entropy and a cross term"),
                StatementSource.FromAuthor(RelativeEntropyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For two density states on the same finite-dimensional carrier, the "
                            + "existing quantum relative entropy is negative von Neumann "
                            + "entropy of the first state minus the real trace of the first "
                            + "state against the logarithm of the second.")),
                    Paragraph(Text(
                        "This is an exact compatibility identity: expanding the relative "
                            + "entropy trace separates its two logarithmic terms, and the "
                            + "self-logarithm term is precisely the negative of the entropy "
                            + "definition."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("basis-pinching-entropy-gain-equals-relative-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/VonNeumannEntropyPinching."
                        + "von_neumann_entropy_pinching"),
                H("Basis pinching gains exactly the relative entropy"),
                StatementSource.FromAuthor(PinchingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B be a complete rank-one record measurement. If applying its "
                            + "basis measurement to a density state rho produces sigma, and "
                            + "the matrix logarithm of sigma is represented in B's diagonal "
                            + "Hermitian subspace, then the entropy of sigma equals the entropy "
                            + "of rho plus their quantum relative entropy.")),
                    Paragraph(Text(
                        "The basis measurement is an orthogonal projection onto the diagonal "
                            + "subspace, so rho and sigma have the same trace pairing against "
                            + "the diagonal logarithm of sigma. Substituting that equality into "
                            + "the relative-entropy decomposition gives the stated exact gain.")),
                    Paragraph(Text(
                        "The result is conditional on diagonal membership of the target "
                            + "logarithm. It does not assert unconditional entropy monotonicity, "
                            + "a data-processing inequality, or nonnegativity of the relative "
                            + "entropy term."))),
                DescribeRole.Theorem))));

    private static Formula RelativeEntropyFormula()
    {
        Formula dimension = F.Id("n");
        Formula densityState = Call("DensityState", dimension);
        Formula entropy = Call("vonNeumannEntropy", Rho);
        Formula crossTerm = Call("ReTr", Seq(Rho, Sp, Call("log", SigmaLower)));

        return Disp(Seq(
            Forall, Sp, dimension, Comma, Sp,
            Rho, Comma, Sp, SigmaLower, Colon, Sp, densityState, Comma, Sp,
            Call("quantumRelativeEntropy", Rho, SigmaLower), Sp, Eq, Sp,
            Minus, entropy, Sp, Minus, Sp, crossTerm, Dot));
    }

    private static Formula PinchingFormula()
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
            recordMeasurement, Sp, Land, Sp,
            pinchedState, Sp, Eq, Sp, SigmaLower, Sp, Land, Sp,
            Call("log", SigmaLower), Sp, InMacro, Sp, diagonalSubspace,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("vonNeumannEntropy", SigmaLower), Sp, Eq, Sp,
            Call("vonNeumannEntropy", Rho), Sp, Plus, Sp,
            Call("quantumRelativeEntropy", Rho, SigmaLower), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
