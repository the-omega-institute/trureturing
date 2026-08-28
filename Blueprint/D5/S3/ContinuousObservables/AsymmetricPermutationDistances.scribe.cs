using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class AsymmetricPermutationDistancesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invariant-label separation for one update and orbit reachability for another produce asymmetric observer distances.",
        H("Asymmetric Permutation Observer Distances"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("asymmetric-permutation-observer-distances"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/AsymmetricPermutationDistances."
                        + "asymmetric_permutation_observer_distances"),
                H("Two permutation observers can assign infinite and finite distance"),
                StatementSource.FromAuthor(Disp(TheoremFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A bounded indicator of the first update's invariant label separates the endpoints, so its scalable zero-defect readout forces infinite distance.")),
                    Paragraph(Text(
                        "For the second update, the signed orbit witness gives a telescoping unit-edge bound. The natural absolute displacement is explicitly finite in the extended nonnegative reals."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("I");
        Formula labelType = F.Id("Leaf");
        Formula firstUpdate = F.Id("tau");
        Formula secondUpdate = F.Id("tauPrime");
        Formula label = F.Id("leaf");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula exponent = F.Id("n");
        Formula displacement = new Formula.Absolute(exponent);

        return Seq(
            Forall, Sp, carrier, Comma, Sp, labelType, Comma, Sp,
            firstUpdate, Comma, Sp, secondUpdate, Sp, InMacro, Sp,
            Call("EquivPerm", carrier), Comma, Sp,
            label, Sp, InMacro, Sp, Call("Map", carrier, labelType), Comma, Sp,
            x, Comma, Sp, y, Sp, InMacro, Sp, carrier, Comma, Sp,
            exponent, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
            Call("InvariantLabel", firstUpdate, label), Sp, Land, Sp,
            label, Open, x, Close, Sp, Neq, Sp, label, Open, y, Close, Sp, Land, Sp,
            x, Sp, Eq, Sp, Call("act", new Formula.Power(secondUpdate, exponent), y),
            Sp, Rightarrow, Sp,
            Call("observerDistance", firstUpdate, x, y), Sp, Eq, Sp, Infty,
            Sp, Land, Sp,
            Call("observerDistance", secondUpdate, x, y), Sp, Leq, Sp, displacement,
            Sp, Land, Sp,
            Call("observerDistance", secondUpdate, x, y), Sp, Lt, Sp, Infty, Dot);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
