using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ZeroSumEnumerationInvarianceDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Weil/ZetaBridge/ZeroSumEnumerationInvariance.";

    public DocumentDefinition Create()
    {
        Formula zeroData = Seq(Operatorname, Grp(F.Id("ZeroData")));
        Formula testFunction = Seq(Operatorname, Grp(F.Id("WeilTestFunction")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula z = F.Id("Z");
        Formula zp = Seq(F.Id("Z"), Apos);
        Formula g = F.Id("g");
        Formula t = F.Id("T");
        Formula h = F.Id("h");
        Formula hp = Seq(F.Id("h"), Apos);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite symmetric zero sums, their convergence, and their limiting value do not "
                + "depend on the duplicate-free exhaustive enumeration of zeta zeros.",
            H("Enumeration Invariance of Symmetric Zero Sums"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("truncated-zero-sum-enumeration-invariance"),
                    DeclarationHandle.Create(Module + "truncatedZeroSum_enum_invariant"),
                    H("Finite symmetric zero sums are enumeration invariant"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, z, Comma, Sp, zp, Colon, Sp, zeroData, Comma, Sp,
                        g, Colon, Sp, testFunction, Comma, Sp,
                        t, Colon, Sp, real, Comma, Sp,
                        Call("truncatedZeroSum", z, g, t), Sp, Eq, Sp,
                        Call("truncatedZeroSum", zp, g, t)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen equivalence from each ZeroData enumeration to the subtype "
                            + "of nontrivial zeta zeros induces a permutation of natural-number "
                            + "indices. It preserves the zero, spectral parameter, multiplicity, "
                            + "symmetric cutoff membership, and summand, so Finset.sum_equiv "
                            + "identifies the two finite sums."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("symmetric-convergence-enumeration-invariance"),
                    DeclarationHandle.Create(Module + "symmetricConvergent_enum_invariant"),
                    H("Symmetric convergence is enumeration invariant"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, z, Comma, Sp, zp, Colon, Sp, zeroData, Comma, Sp,
                        g, Colon, Sp, testFunction, Comma, Sp,
                        Call("SymmetricConvergent", z, g), Sp, Iff, Sp,
                        Call("SymmetricConvergent", zp, g)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each direction transports the same complex limit through the finite-sum "
                            + "enumeration invariance theorem. No summability theorem or new "
                            + "convergence premise is introduced."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zero-sum-enumeration-invariance"),
                    DeclarationHandle.Create(Module + "zeroSum_enum_invariant"),
                    H("The symmetric zero-sum value is enumeration invariant"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, z, Comma, Sp, zp, Colon, Sp, zeroData, Comma, Sp,
                        g, Colon, Sp, testFunction, Comma, Sp,
                        h, Colon, Sp, Call("SymmetricConvergent", z, g), Comma, Sp,
                        hp, Colon, Sp, Call("SymmetricConvergent", zp, g), Comma, Sp,
                        Call("zeroSum", z, g, h), Sp, Eq, Sp,
                        Call("zeroSum", zp, g, hp)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen convergence theorem for the second enumeration is rewritten "
                            + "using finite-sum invariance. The frozen uniqueness theorem for the "
                            + "first zero sum then identifies the two limits, including their "
                            + "possibly different convergence witnesses."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
