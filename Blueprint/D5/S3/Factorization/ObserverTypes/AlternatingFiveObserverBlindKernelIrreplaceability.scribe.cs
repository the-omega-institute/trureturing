using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.ObserverTypes;

internal sealed class AlternatingFiveObserverBlindKernelIrreplaceabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A5 has a full prime-power blind kernel but a faithful "
            + "characteristic-five linear observer.",
        H("Full Blind Kernel and Observer-Type Irreplaceability for A5"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alternating-five-observer-blind-kernel-irreplaceability"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/ObserverTypes/"
                        + "AlternatingFiveObserverBlindKernelIrreplaceability."
                        + "alternating_five_observer_blind_kernel_irreplaceability"),
                H("Prime-power quotient observation leaves A5 fully blind"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a finite group G isomorphic to A5 such that every map from G "
                            + "to every finite p-group is both noninjective and the trivial map. "
                            + "Consequently the canonical prime-power residual is the whole group "
                            + "and the canonical joint quotient observer is constant.")),
                    Paragraph(Text(
                        "For the same group there is an injective characteristic-five linear "
                            + "observer whose kernel is the trivial subgroup. At prime 5 this "
                            + "observer and a prime-power quotient observer have distinct kinds "
                            + "and opposite fidelity."))),
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
        Formula group = F.Id("G");
        Formula alternatingFive = new Formula.Subscript(F.Id("A"), D(5));
        Formula prime = F.Id("p");
        Formula target = F.Id("P");
        Formula quotientObserver = F.Id("q");
        Formula module = F.Id("V");
        Formula residueField = Call("ZMod", D(5));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula linearObserver = Rho;
        Formula blindLocalObserver = new Formula.Subscript(F.Id("o"), F.Id("q"));
        Formula faithfulLocalObserver = new Formula.Subscript(F.Id("o"), Rho);
        Formula top = Call("topSubgroup", group);
        Formula bottom = Call("trivialSubgroup", group);

        Formula primePowerClause = Seq(
            Forall, Sp, prime, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("Prime", prime), Sp, Rightarrow, Sp,
            Forall, Sp, target, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("Group", target), CloseBracket, Comma, Sp,
            OpenBracket, Call("Finite", target), CloseBracket, Comma, Sp,
            Call("IsPGroup", prime, target), Sp, Rightarrow, Sp,
            Forall, Sp, quotientObserver, Sp, InMacro, Sp,
            Call("Hom", group, target), Comma, Sp,
            Open, Neg, Call("Injective", quotientObserver), Sp, Land, Sp,
            Call("IsTrivialHom", quotientObserver), Close);

        Formula residueLinearClause = Seq(
            Exists, Sp, module, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("AddCommGroup", module), CloseBracket, Comma, Sp,
            OpenBracket, Call("Module", residueField, module), CloseBracket, Comma, Sp,
            Exists, Sp, linearObserver, Sp, InMacro, Sp,
            Call("Hom", group, Call("GL", residueField, module)), Comma, Sp,
            Open, Call("Injective", linearObserver), Sp, Land, Sp,
            Equal(Call("kernel", linearObserver), bottom), Close);

        Formula notSingleLocalNotionClause = Seq(
            Exists, Sp, blindLocalObserver, Comma, Sp, faithfulLocalObserver, Sp,
            InMacro, Sp, Call("LocalObserverAtPrime", D(5), group), Comma, Sp,
            Call("Kind", blindLocalObserver), Sp, Eq, Sp,
            F.Id("PrimePowerQuotient"), Sp, Land, Sp,
            Call("Kind", faithfulLocalObserver), Sp, Eq, Sp,
            F.Id("ResidueLinear"), Sp, Land, Sp,
            Call("Kind", blindLocalObserver), Sp, Neq, Sp,
            Call("Kind", faithfulLocalObserver), Sp, Land, Sp,
            Neg, Call("Faithful", blindLocalObserver), Sp, Land, Sp,
            Call("Faithful", faithfulLocalObserver));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp, group, Colon, Sp, type, Comma, Sp,
            OpenBracket, Call("Group", group), CloseBracket, Comma, Sp,
            OpenBracket, Call("Finite", group), CloseBracket, Comma, Sp,
            Call("Nonempty", Call("GroupIso", group, alternatingFive)),
            Sp, Land, RowBreak, Grp(),
            Open, primePowerClause, Close, Sp, Land, RowBreak, Grp(),
            Equal(Call("primePowerResidual", group), top), Sp, Land, RowBreak, Grp(),
            Equal(Call("primePowerQuotientObserver", group), D(1)), Sp, Land, RowBreak, Grp(),
            Open, residueLinearClause, Close, Sp, Land, RowBreak, Grp(),
            Open, notSingleLocalNotionClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
