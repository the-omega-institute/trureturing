using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeAddress;

internal sealed class PrimeAddressDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five prime-address residues connect finite Euler modifications, amplitudes, ramified silence, and loud zeta addresses.",
        H("Prime Address Residues"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-modification-preserves-global-zero-set"),
                DeclarationHandle.Create("D5/S3/Weil/PrimeAddress/PrimeAddress.finite_prime_modification_preserves_global_zero_set"),
                H("Finite prime modifications preserve the global nontrivial zero set"),
                StatementSource.FromAuthor(FiniteModificationStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite set of prime local factors, the modified zeta value vanishes exactly when classical zeta vanishes at every nontrivial zero. The proof uses the frozen finite Euler window zero-free theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-seven-deletion-preserves-nontrivial-zeta-zeros"),
                DeclarationHandle.Create("D5/S3/Weil/PrimeAddress/PrimeAddress.prime_seven_deletion_preserves_nontrivial_zeta_zeros"),
                H("Prime-seven deletion is the finite-modification instance"),
                StatementSource.FromAuthor(PrimeSevenStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This theorem is obtained by instantiating the preceding general result with the singleton prime set containing seven."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-contribution-amplitude-x-beta-cos-gamma-log-x"),
                DeclarationHandle.Create("D5/S3/Weil/PrimeAddress/PrimeAddress.zero_contribution_amplitude_x_beta_cos_gamma_log_x"),
                H("A positive-real zero contribution has cosine amplitude"),
                StatementSource.FromAuthor(ZeroAmplitudeStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive base x, the real part of the complex power with exponent beta plus i gamma is x to the beta times cos(gamma log x)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dirichlet-l-functions-silence-ramified-primes"),
                DeclarationHandle.Create("D5/S3/Weil/PrimeAddress/PrimeAddress.dirichlet_l_functions_silence_ramified_primes"),
                H("Dirichlet characters silence primes ramified by the modulus"),
                StatementSource.FromAuthor(RamifiedPrimeStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Dirichlet character maps a prime residue to zero whenever that prime divides the modulus, by the nonunit mapping law and the ZMod coprimality criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-has-no-silent-prime-address"),
                DeclarationHandle.Create("D5/S3/Weil/PrimeAddress/PrimeAddress.zeta_has_no_silent_prime_address"),
                H("Every zeta prime address is loud"),
                StatementSource.FromAuthor(LoudPrimeAddressStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frozen single-address reading gives log p at a prime power, and Real.log_pos makes this nonzero for every prime."))),
                DescribeRole.Theorem)),
        []));

    private static Formula FiniteModificationStatement() => Disp(Seq(
        Forall, Sp, F.Id("S"), Sp, Colon, Sp,
        Operatorname, Grp(F.Id("Finset")), Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Open, Forall, Sp, F.Id("p"), InMacro, Sp, F.Id("S"), Comma, Sp,
        Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Close,
        Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("s"), Sp, Colon, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
        Operatorname, Grp(F.Id("IsNontrivialZero")), Open, F.Id("s"), Close,
        Sp, Leftrightarrow, Sp,
        Open,
        Operatorname, Grp(F.Id("finitePrimeModification")),
        Open, F.Id("S"), Comma, Sp, F.Id("s"), Close,
        Sp, Eq, Sp, D(0), Sp, Land, Sp,
        D(0), Sp, Lt, Sp, Re, Open, F.Id("s"), Close, Sp, Land, Sp,
        Re, Open, F.Id("s"), Close, Sp, Lt, Sp, D(1),
        Close, Dot));

    private static Formula PrimeSevenStatement() => Disp(Seq(
        Forall, Sp, F.Id("s"), Sp, Colon, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
        Operatorname, Grp(F.Id("IsNontrivialZero")), Open, F.Id("s"), Close,
        Sp, Leftrightarrow, Sp,
        Open,
        Operatorname, Grp(F.Id("finitePrimeModification")),
        Open, OpenBrace, D(7), CloseBrace, Comma, Sp, F.Id("s"), Close,
        Sp, Eq, Sp, D(0), Sp, Land, Sp,
        D(0), Sp, Lt, Sp, Re, Open, F.Id("s"), Close, Sp, Land, Sp,
        Re, Open, F.Id("s"), Close, Sp, Lt, Sp, D(1),
        Close, Dot));

    private static Formula ZeroAmplitudeStatement() => Disp(Seq(
        Forall, Sp, F.Id("x"), Comma, Sp, Beta, Comma, Sp, GammaLower,
        Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("x"), Sp, Rightarrow, Sp,
        Re, Open,
        Open, F.Id("x"), Sp, Colon, Sp, Mathbb, Grp(F.Id("C")), Close,
        Caret, Grp(Open, Beta, Sp, Colon, Sp, Mathbb, Grp(F.Id("C")), Close,
            Sp, Plus, Sp,
            Open, GammaLower, Sp, Colon, Sp, Mathbb, Grp(F.Id("C")), Close,
            Sp, Star, Sp, F.Id("i")),
        Close,
        Sp, Eq, Sp,
        F.Id("x"), Caret, Beta, Sp, Star, Sp,
        Operatorname, Grp(F.Id("cos")),
        Open, GammaLower, Sp, Star, Sp,
        Operatorname, Grp(F.Id("log")), Open, F.Id("x"), Close, Close, Dot));

    private static Formula RamifiedPrimeStatement() => Disp(Seq(
        Forall, Sp, F.Id("R"), Sp, Colon, Sp, F.Id("Type"), Comma, Sp,
        OpenBracket, Operatorname, Grp(F.Id("CommMonoidWithZero")), Sp, F.Id("R"), CloseBracket,
        Comma, Sp, Forall, Sp, F.Id("q"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Forall, Sp, F.Id("chi"), Sp, Colon, Sp,
        Operatorname, Grp(F.Id("DirichletCharacter")), Open, F.Id("R"), Comma, Sp, F.Id("q"), Close,
        Comma, Sp, Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close,
        Sp, Land, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("q"),
        Sp, Rightarrow, Sp,
        F.Id("chi"), Open,
        Open, F.Id("p"), Sp, Colon, Sp,
        Operatorname, Grp(F.Id("ZMod")), Sp, F.Id("q"), Close,
        Close, Sp, Eq, Sp, D(0), Dot));

    private static Formula LoudPrimeAddressStatement() => Disp(Seq(
        Forall, Sp, F.Id("p"), Comma, Sp, F.Id("k"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp,
        Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close,
        Sp, Land, Sp, F.Id("k"), Sp, Neq, Sp, D(0),
        Sp, Rightarrow, Sp,
        Operatorname, Grp(F.Id("singleAddressReading")),
        Open, F.Id("p"), Caret, F.Id("k"), Close,
        Sp, Neq, Sp, D(0), Dot));
}
