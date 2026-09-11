using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class FiniteDivisorPartitionZerosDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite divisor partition functions have explicit local zeros and no zeros off the imaginary axis.",
        H("Zeros of finite divisor partition functions"),
        Blocks(
            Entry("localFactor", "A finite geometric factor",
                "For a natural base p and exponent a, sum the powers of p to minus s "
                    + "from degree zero through degree a. The exponent a may be zero.",
                Eqn(Factor, Seq(Sum, Underscore, Grp(F.Id("j"), Eq, Num(0)),
                    Caret, Grp(A), Sp, Pow(Pow(P, Seq(Minus, S)), F.Id("j")))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Factorization/dlmf2026divisorpartition")), DescribeRole.Definition),
            Entry("partition", "The finite divisor partition function",
                "For a positive integer N, multiply the local factors over its distinct "
                    + "prime divisors. The exponent in each factor is that prime's multiplicity "
                    + "in N. For N equal to one the empty product is one.",
                Eqn(Partition, Seq(Prod, Underscore,
                    Grp(P, Sp, Mid, Sp, F.Id("N"), Comma, Sp, Call("Prime", P)), Sp,
                    Call("localFactor", P, Call("factorization", F.Id("N"), P), S))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Factorization/dlmf2026divisorpartition")), DescribeRole.Definition),
            Entry("local_factor_eq_zero_iff", "The exact local zero lattice",
                "Let p be prime and a a natural number. A zero has the form two pi i k "
                    + "divided by (a+1) log p, where k is an integer not divisible by a+1. "
                    + "The finite geometric sum vanishes precisely when its ratio has "
                    + "(a+1)-st power one but is not one. Solving the exponential equation "
                    + "gives the lattice; excluding ratio one removes exactly the divisible "
                    + "indices. When a is zero, there are no such indices.",
                Disp(Seq(Factor, Sp, Eq, Sp, Num(0), Sp, Iff, Sp,
                    Exists, Sp, F.Id("k"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    S, Sp, Eq, Sp, Phase, Sp, Land, Sp,
                    Neg, Open, A, Plus, Num(1), Sp, Mid, Sp, F.Id("k"), Close)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Factorization/mathlib2026finitedivisorzeros"))),
            Entry("local_factor_zero_re", "A local zero has real part zero",
                "A root of unity has modulus one. The modulus of p to minus s is p "
                    + "to minus the real part of s. Since a prime p is greater than one, "
                    + "injectivity of the real exponential forces the real part to be zero.",
                Disp(Seq(Factor, Sp, Eq, Sp, Num(0), Sp, Rightarrow, Sp,
                    RealPart, Sp, Eq, Sp, Num(0))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Factorization/dlmf2026divisorpartition"))),
            Entry("partition_ne_zero_of_re_ne_zero", "Nonvanishing away from the imaginary axis",
                "If the real part of s is nonzero, every local factor is nonzero. "
                    + "A finite product of nonzero complex numbers is nonzero.",
                Disp(Seq(RealPart, Sp, Neq, Sp, Num(0), Sp, Rightarrow, Sp,
                    Partition, Sp, Neq, Sp, Num(0))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Factorization/dlmf2026divisorpartition"))),
            Entry("partition_zero_re", "Every zero lies on the imaginary axis",
                "Apply the nonvanishing statement contrapositively to the same finite "
                    + "divisor partition function.",
                Disp(Seq(Partition, Sp, Eq, Sp, Num(0), Sp, Rightarrow, Sp,
                    RealPart, Sp, Eq, Sp, Num(0))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Factorization/dlmf2026divisorpartition"))))));

    private static DocumentBlock Entry(string declaration, string title, string prose,
        Formula formula, AssessedProvenance provenance, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("finite-divisor-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + declaration), H(title), StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula P => F.Id("p");
    private static Formula A => F.Id("a");
    private static Formula S => F.Id("s");
    private static Formula Factor => Call("localFactor", P, A, S);
    private static Formula Partition => Call("partition", F.Id("N"), S);
    private static Formula RealPart => Seq(Re, Sp, S);
    private static Formula Phase => Seq(Frac,
        Grp(Num(2), Sp, Pi, Sp, F.Id("i"), Sp, F.Id("k")),
        Grp(Open, A, Plus, Num(1), Close, Sp, Log, Sp, P));
    private static Formula Pow(Formula x, Formula n) => Seq(Grp(x), Caret, Grp(n));
    private static Formula Eqn(Formula x, Formula y) => Disp(Seq(x, Sp, Eq, Sp, y));
}
