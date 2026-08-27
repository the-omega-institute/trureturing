using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.ObserverTypes;

internal sealed class AlternatingFiveObserverTypeIrreplaceabilityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A5 is invisible to every finite p-group observer but has a faithful characteristic-five linear observer.",
        H("Observer-Type Irreplaceability for A5"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alternating-five-observer-type-irreplaceability"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/ObserverTypes/"
                        + "AlternatingFiveObserverTypeIrreplaceability."
                        + "alternating_five_observer_type_irreplaceability"),
                H("Prime-power quotient and residue-linear observers are not interchangeable"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a finite group G isomorphic to A5 such that, for every prime p, "
                            + "every finite p-group P, and every homomorphism from G to P, the "
                            + "homomorphism is noninjective. This universal clause is inherited "
                            + "from the repository theorem that all such homomorphisms are trivial.")),
                    Paragraph(Text(
                        "For the same group G there is a module V over Z/5Z and an injective "
                            + "homomorphism from G to the general linear group of V. The witness "
                            + "is the left regular representation, so the existential observer is "
                            + "constructed rather than postulated."))),
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
        Formula linearObserver = Rho;

        Formula primePowerClause = Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("Prime", prime), Sp, Rightarrow, Sp,
            Forall, Sp, target, Comma, Sp,
            Open,
            Call("FiniteGroup", target), Sp, Land, Sp,
            Call("IsPGroup", prime, target),
            Close, Sp, Rightarrow, Sp,
            Forall, Sp, quotientObserver, Sp, InMacro, Sp,
            Call("Hom", group, target), Comma, Sp,
            Neg, Call("Injective", quotientObserver));

        Formula residueLinearClause = Seq(
            Exists, Sp, module, Comma, Sp,
            Call("Module", residueField, module), Sp, Land, Sp,
            Exists, Sp, linearObserver, Sp, InMacro, Sp,
            Call("Hom", group, Call("GL", residueField, module)), Comma, Sp,
            Call("Injective", linearObserver));

        return Disp(Seq(
            Exists, Sp, group, Comma, Sp,
            Call("FiniteGroup", group), Sp, Land, Sp,
            Call("GroupIso", group, alternatingFive), Sp, Land, RowBreak, Grp(),
            Open, primePowerClause, Close, Sp, Land, RowBreak, Grp(),
            Open, residueLinearClause, Close, Dot));
    }
}
