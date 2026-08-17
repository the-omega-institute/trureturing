using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class CoordinateSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint linear coordinates separate points exactly when their common kernels are trivial.",
        H("Coordinate Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-linear-coordinates-separate-exactly-at-trivial-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/CoordinateSeparation."
                    + "coordinate_separation_criterion"),
                H("Joint coordinates separate exactly at trivial common kernel"),
                StatementSource.FromAuthor(CoordinateSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be an indexed family of linear maps from one module M into modules "
                            + "N_i. Its joint coordinate map sends a point to all q_i values.")),
                    Paragraph(Text(
                        "The joint map is injective exactly when the infimum of its component "
                            + "Setoid kernels is the diagonal relation and the infimum of its "
                            + "component linear kernels is the zero submodule.")),
                    Paragraph(Text(
                        "This closes theorem/30.6 from qdo-v1 in its linear form. The bottom "
                            + "Setoid is literal equality, so the first condition is the source "
                            + "criterion that the limiting indistinguishability relation is the "
                            + "diagonal; the second is its linear common-kernel equivalent.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplied Setoid.injective_iff_ker_bot, "
                            + "LinearMap.ker_pi, and LinearMap.ker_eq_bot_of_injective, all applied "
                            + "by the Lean proof. Loogle returned the first two identities; local "
                            + "source search found the linear helper. D5 search found no equivalent "
                            + "separation theorem. LeanSearch's API returned HTTP 404 and supplied "
                            + "no conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula IndexedInfimum(Formula index) =>
        Seq(Operatorname, Grp(F.Id("iInf")), Underscore,
            Grp(Seq(F.Id("i"), Sp, InMacro, Sp, index)));

    private static Formula CoordinateSeparationFormula()
    {
        Formula ring = F.Id("R");
        Formula source = F.Id("M");
        Formula index = F.Id("I");
        Formula target = F.Id("N");
        Formula coordinate = F.Id("q");
        Formula component = F.Id("i");
        Formula coordinateAt = Seq(coordinate, Underscore, Grp(component));
        Formula targetAt = Seq(target, Underscore, Grp(component));
        Formula joint = Apply(F.Id("pi"), coordinate);
        Formula setoidKernel = Seq(
            IndexedInfimum(index), Sp,
            Apply(Seq(Ker, Underscore, Grp(F.Id("Setoid"))), coordinateAt));
        Formula linearKernel = Seq(
            IndexedInfimum(index), Sp,
            Apply(Seq(Ker, Underscore, Grp(F.Id("Linear"))), coordinateAt));

        return Disp(Seq(
            Forall, Sp, ring, Comma, Sp, source, Comma, Sp, index, Comma, Sp, target,
            Comma, Esc,
            coordinate, Colon, Sp, Prod, Underscore, Grp(component), Sp,
            Open, source, Sp, To, Sp, targetAt, Close, Comma, Esc,
            Call("Injective", joint), Sp, Iff, Sp,
            Open, setoidKernel, Sp, Eq, Sp, Delta, Underscore, Grp(source), Close,
            Sp, Land, Sp,
            Open, linearKernel, Sp, Eq, Sp, OpenBrace, D(0), CloseBrace, Close,
            Dot));
    }
}
