using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class QubitWitnessesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Schwinger = LibraryNoteRef.Create("D5/L/schwinger1960unitary");
    private static readonly LibraryNoteRef Zurek = LibraryNoteRef.Create("D5/L/zurek2003decoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/QubitWitnesses",
            "Explicit qubit incompatibility, entanglement, and dephasing witnesses."),
        H("Qubit Witness Skeletons"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("pauli-x-and-z-have-no-nonzero-common-eigenvector"),
                H("Pauli X and Z have no nonzero common eigenvector"),
                LeanTheorem("D5/S3/Quantum/QubitWitnesses.pauli_observables_have_no_common_eigenvector"),
                Disp(Seq(Forall, Sp, Psi, InMacro, Mathbb, Grp(F.Id("C")), Caret, Grp(D(2)), Comma, Esc, Forall, Sp, F.Id("x"), Comma, F.Id("z"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Open, F.Id("X"), Psi, Eq, F.Id("x"), Psi, Sp, Land, Sp, F.Id("Z"), Psi, Eq, F.Id("z"), Psi, Close, Sp, Rightarrow, Sp, Psi, Eq, D(0))),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The standard Pauli X and Z observables have no nonzero common eigenvector on C^2. This is an explicit incompatibility witness only: it does not prove the Robertson variance inequality, arbitrary-window full-matrix generation, prime-power tensor factorization, general qudit Weyl relations, or any classical ontology forcing the structure. Original numerical-certificate claim not formalized: the source atom's full matrix-unit relations with exact zero certificate error.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-bell-coefficient-matrix-is-not-a-simple-tensor"),
                H("The Bell coefficient matrix is not a simple tensor"),
                LeanTheorem("D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product"),
                In(Seq(Neg, Exists, Sp, Ell, Comma, F.Id("r"), InMacro, Mathbb, Grp(F.Id("C")), Caret, Grp(D(2)), Comma, Esc, Operatorname, Grp(F.Id("productCoefficients")), Open, Ell, Comma, F.Id("r"), Close, Eq, Operatorname, Grp(F.Id("bellCoefficients")))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The coefficient matrix of the unnormalized Bell vector |00> + |11> cannot be factored as an outer product. A nonzero normalization scalar does not change this obstruction. This elementary algebraic witness is proved directly in the repository; Bell's 1964 paper treats the spin singlet and locality, not this exact vector or factorization argument. This declaration proves neither a CHSH expectation nor Tsirelson optimality, a local-hidden-variable bound, Kochen-Specker contextuality, hidden-address interpretations, or that probability is not ignorance. Original numerical-certificate claims not formalized: the source atom's CHSH values 2*sqrt(2) = 2.8284 and the classical local-fiber bound 2.0.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("iterated-phase-damping-has-the-exact-qubit-certificate"),
                H("Iterated phase damping has the exact qubit certificate"),
                LeanTheorem("D5/S3/Quantum/QubitWitnesses.equal_superposition_phase_damping_certificate"),
                Disp(Seq(Forall, Sp, F.Id("c"), InMacro, OpenBracket, D(0), Comma, D(1), CloseBracket, Comma, Esc, Forall, Sp, F.Id("N"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, Rho, Underscore, Grp(F.Id("N")), Colon, Eq, Operatorname, Grp(F.Id("phaseDampingIterate")), Open, F.Id("c"), Comma, F.Id("N"), Comma, Operatorname, Grp(F.Id("equalSuperpositionDensity")), Close, Comma, Esc, Open, Rho, Underscore, Grp(F.Id("N")), Close, Underscore, Grp(D(0, 0)), Eq, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, Sp, Open, Rho, Underscore, Grp(F.Id("N")), Close, Underscore, Grp(D(1, 1)), Eq, Frac, Grp(D(1)), Grp(D(2)), Sp, Land, Sp, Open, Rho, Underscore, Grp(F.Id("N")), Close, Underscore, Grp(D(0, 1)), Eq, Frac, Grp(D(1)), Grp(D(2)), F.Id("c"), Caret, Grp(F.Id("N")), Sp, Land, Sp, Open, Rho, Underscore, Grp(F.Id("N")), Close, Underscore, Grp(D(1, 0)), Eq, Frac, Grp(D(1)), Grp(D(2)), F.Id("c"), Caret, Grp(F.Id("N")))),
                DescribeProvenance.LiteratureAttested(Zurek),
                Blocks(Paragraph(Text(
                    "For the standard real phase-damping map with retention coefficient c in [0,1], N repetitions leave both equal-superposition populations at one half and multiply both coherence entries by c^N. The map is assumed, not derived from a system-environment Hamiltonian. The declaration does not identify this repository's ledger with an environment, bookkeeping with decoherence, or address selection with einselection. Original certificate coverage: the source atom's symbolic (1/2) * c0^N coherence law and fixed one-half populations are formalized exactly; the atom supplies no fixed numeric c0 or N.")))
            ))));
}
