using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class CayleyNevanlinnaKernelEquivalenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/CayleyNevanlinnaKernelEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "A positive shifted Cayley transform identifies the de Branges "
                + "and Nevanlinna kernels through an invertible diagonal gauge.",
            H("Cayley Equivalence of de Branges and Nevanlinna Kernels"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("cayley-nevanlinna-kernel-identity"),
                    DeclarationHandle.Create(
                        Prefix + "cayley_nevanlinna_kernel_identity"),
                    H("Exact pointwise gauge identity"),
                    StatementSource.FromAuthor(IdentityFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For omega > 0 and 1 + theta(x) nonzero, direct "
                                + "Cayley algebra gives the exact factor "
                                + "4 pi / omega and the two nonvanishing gauge "
                                + "denominators.")),
                        Paragraph(Text(
                            "No cross-denominator premise is needed. If "
                                + "z - conjugate(w) vanishes, both totalized "
                                + "kernel quotients are zero; otherwise the "
                                + "ordinary field calculation applies."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("cayley-nevanlinna-kernel-psd-equivalence"),
                    DeclarationHandle.Create(
                        Prefix + "cayley_nevanlinna_kernel_posSemidef_iff"),
                    H("Finite Gram positivity is equivalent"),
                    StatementSource.FromAuthor(PositivityFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "On every finite sample, the Nevanlinna Gram matrix is "
                            + "U K U* where U is the diagonal gauge containing "
                            + "sqrt(4 pi / omega). Positivity of omega and "
                            + "nonvanishing of 1 + theta make U invertible, so "
                            + "positive semidefiniteness holds in both directions."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("cayley-kernel-gauge-degeneracy"),
                    DeclarationHandle.Create(
                        Prefix + "gauge_nonvanishing_is_necessary"),
                    H("A vanishing gauge denominator breaks the identity"),
                    StatementSource.FromAuthor(DegeneracyFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The explicit function theta(0) = -1 and theta(x) = 0 "
                            + "away from zero makes the Cayley quotient totalize "
                            + "to zero at one endpoint while the uncancelled "
                            + "Nevanlinna difference remains nonzero. Thus the "
                            + "gauge premise cannot be omitted."))),
                    DescribeRole.Theorem))));

    private static Formula IdentityFormula()
    {
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        Formula thetaZ = Call("theta", z);
        Formula thetaWBar = Seq(Overline, Grp(Call("theta", w)));
        Formula denominator = Seq(
            Open, D(1), Plus, thetaZ, Close,
            Open, D(1), Plus, thetaWBar, Close);
        Formula scale = new Formula.Fraction(
            Seq(D(4), Pi), F.Id("omega"));
        return Disp(Seq(
            F.Id("omega"), Gt, D(0), Comma, Sp,
            Forall, Sp, F.Id("x"), Comma, Sp,
            D(1), Plus, Call("theta", F.Id("x")), Neq, D(0),
            Sp, Rightarrow, Sp,
            Call("nevanlinnaKernel", z, w), Eq,
            new Formula.Fraction(
                Seq(scale, Call("deBrangesKernel", z, w)), denominator), Dot));
    }

    private static Formula PositivityFormula() => Disp(Seq(
        F.Id("omega"), Gt, D(0), Comma, Sp,
        Forall, Sp, F.Id("x"), Comma, Sp,
        D(1), Plus, Call("theta", F.Id("x")), Neq, D(0),
        Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("n"), Comma, Sp, F.Id("z"), Underscore, D(1),
        Comma, Sp, Cdot, Comma, Sp, F.Id("z"), Underscore, F.Id("n"), Comma, Sp,
        Call("PosSemidef", Seq(OpenBracket,
            Call("deBrangesKernel",
                Seq(F.Id("z"), Underscore, F.Id("i")),
                Seq(F.Id("z"), Underscore, F.Id("j"))), CloseBracket)),
        Sp, Leftrightarrow, Sp,
        Call("PosSemidef", Seq(OpenBracket,
            Call("nevanlinnaKernel",
                Seq(F.Id("z"), Underscore, F.Id("i")),
                Seq(F.Id("z"), Underscore, F.Id("j"))), CloseBracket)), Dot));

    private static Formula DegeneracyFormula() => Disp(Seq(
        Call("theta", D(0)), Eq, Minus, D(1), Comma, Sp,
        Forall, Sp, F.Id("x"), Neq, D(0), Comma, Sp,
        Call("theta", F.Id("x")), Eq, D(0), Sp, Rightarrow, Sp,
        Call("nevanlinnaKernel", D(0), D(1)), Neq,
        new Formula.Fraction(
            Seq(D(4), Pi, Call("deBrangesKernel", D(0), D(1))),
            Seq(Open, D(1), Plus, Call("theta", D(0)), Close,
                Open, D(1), Plus, Overline, Grp(Call("theta", D(1))), Close)),
        Dot));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
