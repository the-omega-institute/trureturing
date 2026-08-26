using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class AlternatingFiveResidualSeparationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power quotient observations of A5 are strictly weaker than all finite quotients.",
        H("Prime-Power and Finite-Quotient Separation for A5"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alternating-five-residual-separation"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/PrimePowers/"
                        + "AlternatingFiveResidualSeparation."
                        + "alternating_five_residual_separation"),
                H("Prime-power observations of A5 are completely blind"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every prime p, the fixed-prime residual constructed from all "
                            + "finite p-group quotient channels is the whole alternating group "
                            + "A5. The canonical residual over all primes is likewise the whole "
                            + "group, and its canonical joint observer is the trivial map.")),
                    Paragraph(Text(
                        "The all-finite quotient family contains a channel whose kernel is the "
                            + "trivial subgroup, representing the identity finite quotient. "
                            + "Consequently its canonical residual is trivial and is strictly "
                            + "smaller than the prime-power residual."))),
                DescribeRole.Theorem))));

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

    private static Formula TheoremFormula()
    {
        Formula alternatingFive = new Formula.Subscript(F.Id("A"), D(5));
        Formula prime = F.Id("p");
        Formula fixedResidual = Call("pGroupResidual", prime, alternatingFive);
        Formula allPrimeResidual = Call("primePowerResidual", alternatingFive);
        Formula allPrimeObserver = Call("primePowerQuotientObserver", alternatingFive);
        Formula allFiniteResidual = Call("finiteResidual", alternatingFive);
        Formula top = Call("topSubgroup", alternatingFive);
        Formula bottom = Call("trivialSubgroup", alternatingFive);
        Formula identityChannel = F.Id("H");

        Formula fixedPrimeClause = Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("Prime", prime), Sp, Rightarrow, Sp,
            Equal(fixedResidual, top));
        Formula identityClause = Seq(
            Exists, Sp, identityChannel, Sp, InMacro, Sp,
            Call("FiniteQuotientIndex", alternatingFive), Comma, Sp,
            Equal(Call("kernel", identityChannel), bottom));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, fixedPrimeClause, Close, Sp, Land, RowBreak, Grp(),
            Equal(allPrimeResidual, top), Sp, Land, RowBreak, Grp(),
            Equal(allPrimeObserver, D(1)), Sp, Land, RowBreak, Grp(),
            Open, identityClause, Close, Sp, Land, RowBreak, Grp(),
            Equal(allFiniteResidual, bottom), Sp, Land, RowBreak, Grp(),
            allFiniteResidual, Sp, Lt, Sp, allPrimeResidual, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
