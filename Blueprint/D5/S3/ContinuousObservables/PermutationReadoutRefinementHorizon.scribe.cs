using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class PermutationReadoutRefinementHorizonDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ContinuousObservables/PermutationReadoutRefinementHorizon."
            + "permutation_readout_refinement_horizon";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Readout refinement grows permutation horizons up to the full cyclic-orbit bound, "
            + "while changing the update changes that bound.",
        H("Permutation Readout Refinement and Horizon Bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("permutation-readout-refinement-horizon"),
            DeclarationHandle.Create(Declaration),
            H("Readout refinement stays within the orbit bound"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a fixed permutation, every chosen family of bounded unit-edge "
                        + "readouts has horizon inside the complement of the origin's cyclic "
                        + "orbit. Inclusion of readout families enlarges the horizon, and the "
                        + "full admissible family attains the orbit-complement bound.")),
                Paragraph(Text(
                    "Changing the permutation changes the orbit bound: a point outside the old "
                        + "orbit but inside the new orbit has infinite old full-family distance "
                        + "and finite new full-family distance.")),
                Paragraph(Text(
                    "The strict-refinement example corrects the literal source example. One "
                        + "bounded orbit indicator has only finite oscillation, so it cannot by "
                        + "itself create infinite distance. The formal witness adjoins every real "
                        + "scalar multiple of the indicator; their supremum is infinite."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("I");
        Formula firstUpdate = F.Id("tau");
        Formula secondUpdate = F.Id("tauPrime");
        Formula origin = F.Id("o");
        Formula oldFamily = F.Id("A");
        Formula newFamily = F.Id("B");
        Formula point = F.Id("y");
        Formula exampleUpdate = F.Id("sigma");
        Formula exampleOld = F.Id("C");
        Formula exampleNew = F.Id("D");
        Formula firstReadouts = Call("Read", firstUpdate);
        Formula firstOrbit = Call("Orb", firstUpdate, origin);
        Formula secondOrbit = Call("Orb", secondUpdate, origin);
        Formula firstComplement = Seq(carrier, Sp, Setminus, Sp, firstOrbit);
        Formula fullHorizon = Call("H", firstUpdate, firstReadouts, origin);

        Formula familyBound = Seq(
            Forall, Sp, oldFamily, Sp, Subseteq, Sp, firstReadouts, Comma, Sp,
            Call("H", firstUpdate, oldFamily, origin), Sp, Subseteq, Sp,
            firstComplement);

        Formula refinement = Seq(
            Forall, Sp, oldFamily, Comma, Sp, newFamily, Sp, Subseteq, Sp,
            firstReadouts, Comma, Sp,
            oldFamily, Sp, Subseteq, Sp, newFamily, Sp, Rightarrow, Sp,
            Call("H", firstUpdate, oldFamily, origin), Sp, Subseteq, Sp,
            Call("H", firstUpdate, newFamily, origin));

        Formula updateChange = Seq(
            Forall, Sp, point, Sp, InMacro, Sp,
            secondOrbit, Sp, Setminus, Sp, firstOrbit, Comma, Sp,
            point, Sp, InMacro, Sp, fullHorizon, Sp, Land, Sp,
            Call("d", secondUpdate, origin, point), Sp, Lt, Sp, Infty);

        Formula strictWitness = Seq(
            Exists, Sp, exampleUpdate, Sp, InMacro, Sp,
            Call("EquivPerm", F.Id("Bool")), Comma, Sp,
            exampleOld, Comma, Sp, exampleNew, Sp, Subseteq, Sp,
            Call("Read", exampleUpdate), Comma, Sp,
            exampleOld, Sp, Subseteq, Sp, exampleNew, Sp, Land, Sp,
            Call("H", exampleUpdate, exampleOld, F.Id("false")), Sp, Eq, Sp,
            Emptyset, Sp, Land, Sp,
            F.Id("true"), Sp, InMacro, Sp,
            Call("H", exampleUpdate, exampleNew, F.Id("false")));

        return Seq(
            Forall, Sp, carrier, Comma, Sp,
            firstUpdate, Comma, Sp, secondUpdate, Sp, InMacro, Sp,
            Call("EquivPerm", carrier), Comma, Sp,
            origin, Sp, InMacro, Sp, carrier, Comma, Esc,
            Open, familyBound, Close, Sp, Land, Esc,
            Open, refinement, Close, Sp, Land, Esc,
            fullHorizon, Sp, Eq, Sp, firstComplement, Sp, Land, Esc,
            Open, updateChange, Close, Sp, Land, Esc,
            Open, strictWitness, Close, Dot);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)) };
        if (arguments.Length == 0)
        {
            return Seq([.. items]);
        }

        items.Add(Open);
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
