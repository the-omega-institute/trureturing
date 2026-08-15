using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.NicaCovariance;

internal sealed class PureShiftVacuumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nontrivial arithmetic translations are pure isometries, while simultaneous Euler "
        + "sieving by all prime addresses leaves exactly the vacuum line.",
        H("Pure Shift and the Euler-Sieve Vacuum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nontrivial-arithmetic-shifts-have-no-unitary-tail"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/PureShiftVacuum."
                    + "iInf_divisibleSubspace_tablePow_eq_bot"),
                H("Nontrivial arithmetic shifts have no unitary tail"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    F.Id("u"), Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("vacuumAddress")), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("iInf")), Underscore, Grp(
                        F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N"))), Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")), Open,
                    Operatorname, Grp(F.Id("tablePow")), Open,
                    F.Id("u"), Comma, Sp, F.Id("n"), Close, Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("bot"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The address tablePow u n encodes the n-th power of the positive integer "
                    + "encoding of u. For any fixed coefficient address b, a nontrivial base "
                    + "power eventually exceeds b and therefore cannot divide it. Membership in "
                    + "every divisible subspace consequently forces every coefficient to vanish, "
                    + "so the common tail is the zero subspace."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-euler-sieve-leaves-exactly-the-vacuum-line"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/PureShiftVacuum."
                    + "iInf_orthogonal_divisibleSubspace_primeAddress_eq_vacuum"),
                H("The Euler sieve leaves exactly the vacuum line"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("iInf")), Underscore, Grp(
                        F.Id("p"), InMacro, Sp,
                        Operatorname, Grp(F.Id("NatPrimes"))), Sp,
                    Open, Operatorname, Grp(F.Id("divisibleSubspace")), Open,
                    Operatorname, Grp(F.Id("primeAddress")), Open,
                    F.Id("p"), Close, Close, Close, Caret, Grp(Perp),
                    Sp, Eq, Sp, Mathbb, Grp(F.Id("C")), Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("vacuumKet"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A coefficient family in every prime wandering complement vanishes at each "
                    + "non-vacuum address: the positive integer encoded by that address has a "
                    + "prime divisor, and the corresponding orthogonal-complement condition kills "
                    + "the coefficient. The address one has no prime divisor, so its ket survives "
                    + "every sieve and spans the entire intersection."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/NicaCovariance/DoubleCommutation")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/NicaCovariance/SemigroupRelations")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint")),
        ]));
}
