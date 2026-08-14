using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class TsirelsonTightnessDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Cirelson =
        LibraryNoteRef.Create("D5/L/Quantum/cirelson1980quantum");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive Tsirelson value is the attained maximum state expectation of the fixed CHSH witness.",
        H("Tightness of the Fixed CHSH Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-positive-tsirelson-value-is-the-greatest-fixed-witness-expectation"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/TsirelsonTightness.bell_chsh_state_expectation_is_greatest"),
                H("The positive Tsirelson value is the greatest fixed-witness expectation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsGreatest")), Open,
                    Left, OpenBrace,
                    Re, Open, Operatorname, Grp(F.Id("tr")), Open,
                    Rho, Sp, F.Id("S"), Close, Close, Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("tr")), Open, Rho, Close, Eq, D(1),
                    Right, CloseBrace, Comma, Esc,
                    D(2), Sp, Sqrt, Grp(D(2)), Close, Dot))),
                AssessedProvenance.FromLiterature(Cirelson),
                Blocks(
                    Paragraph(Text(
                        "Fix S to be CHSHWitness.chshOperator, built from the Pauli Z and X " +
                        "observables and the two fixed Bob observables of CHSHWitness. Among " +
                        "positive-semidefinite two-qubit matrices rho with trace one, the real " +
                        "trace expectation Re(tr(rho S)) has greatest value two times square " +
                        "root two. The IsGreatest conclusion includes both attainment and the " +
                        "upper bound for every state in this fixed state space.")),
                    Paragraph(Text(
                        "Attainment is supplied by CHSHWitness.bellDensity and the exact " +
                        "calculation CHSHWitness.bell_chsh_value. For the upper-bound half, the " +
                        "proof rewrites S as the CHSH combination of the lifted observables, " +
                        "applies mathlib's tsirelson_inequality to their certified CHSH tuple, " +
                        "and transports the resulting matrix order through the positive trace " +
                        "pairing with rho.")),
                    Paragraph(Text(
                        "The value and its sharpness are the classical Tsirelson bound, attested " +
                        "by B. S. Cirel'son, Quantum generalizations of Bell's inequality, " +
                        "Letters in Mathematical Physics 4 (1980), 93-100. The declaration does " +
                        "not characterize maximizing states, prove a converse, or optimize over " +
                        "varying observables: the four observables and S are fixed throughout."))),
                DescribeRole.Theorem))));
}
