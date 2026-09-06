using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class CHSHWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("A normalized Bell state and fixed Pauli observables attain the positive Tsirelson value.",
        H("A Tight CHSH Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-bell-density-is-a-normalized-positive-state"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state"),
                H("The Bell density is a normalized positive state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("PosSemidef")), Open,
                    Rho, Underscore, Grp(F.Id("Bell")), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("tr")), Open,
                    Rho, Underscore, Grp(F.Id("Bell")), Close, Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalized Bell vector defines a rank-one positive semidefinite "
                        + "density matrix. Its trace is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bobs-fixed-observables-are-self-adjoint-involutions"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.bob_observables_are_valid"),
                H("Bob's fixed observables are self-adjoint involutions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("j"), InMacro, OpenBrace, D(0), Comma, D(1), CloseBrace,
                    Comma, Esc, F.Id("B"), Underscore, F.Id("j"), Caret, Grp(Star),
                    Eq, F.Id("B"), Underscore, F.Id("j"), Sp, Land, Sp,
                    F.Id("B"), Underscore, F.Id("j"), Caret, Grp(D(2)), Eq, F.Id("I")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Bob's sum and difference of the Pauli Z and X matrices, each divided "
                        + "by square root two, are self-adjoint and square to the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-kronecker-operator-equals-the-lifted-chsh-combination"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.chsh_operator_eq_lifted_chsh"),
                H("The Kronecker operator equals the lifted CHSH combination"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("S"), Eq,
                    Lifted("A", 0), Lifted("B", 0), Plus,
                    Lifted("A", 0), Lifted("B", 1), Plus,
                    Lifted("A", 1), Lifted("B", 0), Minus,
                    Lifted("A", 1), Lifted("B", 1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lift Alice's observables by tensoring on the right with the identity, "
                        + "and Bob's by tensoring on the left. The original sum of Kronecker "
                        + "products is exactly the CHSH combination of these lifted matrices; "
                        + "the superscript L denotes this lift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-lifted-observables-satisfy-the-chsh-tuple-conditions"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.lifted_observables_form_chsh_tuple"),
                H("The lifted observables satisfy the CHSH tuple conditions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsCHSHTuple")), Open,
                    Lifted("A", 0), Comma, Lifted("A", 1), Comma,
                    Lifted("B", 0), Comma, Lifted("B", 1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four lifted observables are self-adjoint involutions in the "
                        + "two-qubit matrix algebra. Each lifted Alice observable commutes "
                        + "with each lifted Bob observable, as required by IsCHSHTuple."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-bell-witness-attains-the-positive-tsirelson-value"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value"),
                H("The Bell witness attains the positive Tsirelson value"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("tr")), Open,
                    Rho, Underscore, Grp(F.Id("Bell")), Sp, F.Id("S"), Close,
                    Eq, D(2), Sqrt, Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A0 be the Pauli Z matrix and A1 the Pauli X matrix. Let B0 be " +
                        "the sum of Pauli Z and Pauli X divided by square root two, and let " +
                        "B1 be their difference divided by square root two. The named matrix S " +
                        "is the CHSH combination of the four corresponding Kronecker products. " +
                        "The state rhoBell is the rank-one density matrix obtained by flattening " +
                        "the existing bellCoefficients matrix and normalizing it by square root two.")),
                    Paragraph(Text(
                        "The checked trace is exactly positive two times square root two. The " +
                        "companion Lean certificate bell_density_is_state proves that rhoBell is " +
                        "positive semidefinite with trace one, while bob_observables_are_valid " +
                        "proves that B0 and B1 are self-adjoint involutions. Thus the equality is " +
                        "a qualified state-observable witness, not an unnormalized matrix identity.")),
                    Paragraph(Text(
                        "Mathlib's tsirelson_inequality is the upstream source for the general CHSH " +
                        "upper bound. This declaration establishes only its explicit finite-dimensional " +
                        "tightness witness: it introduces no operator norm, eigenvalue classification, " +
                        "spectral order, C-star matrix instance, or second proof of the upper bound."))),
                DescribeRole.Theorem))));

    private static Formula Lifted(string observable, byte setting) => Seq(
        F.Id(observable), Underscore, D(setting), Caret, Grp(F.Id("L")));
}
