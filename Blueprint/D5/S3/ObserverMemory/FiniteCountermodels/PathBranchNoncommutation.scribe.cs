using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FiniteCountermodels;

internal sealed class PathBranchNoncommutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary backward paths retain periodic dynamics but discard transient branches.",
        H("Path Limits and Transient Branches"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("path-limit-branch-noncommutation"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/FiniteCountermodels/PathBranchNoncommutation."
                    + "path_limit_branch_noncommutation"),
                H("The same periodic path limit can carry different complete branch trees"),
                StatementSource.FromAuthor(NoncommutationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "BackwardOrbit is the repository's compatible predecessor-path type. "
                            + "The displayed backward equivalence is constructed by evaluating "
                            + "at coordinate zero, transporting through an equivalence of "
                            + "periodic cores, and applying the inverse canonical path map.")),
                    Paragraph(Text(
                        "TransientChild(tau,p) is constructed from the source update: it "
                            + "contains exactly the nonperiodic x with tau(x)=p. The concrete "
                            + "constant maps on Fin 2 and Fin 3 have one-point periodic cores. "
                            + "Every transient child is a leaf, while their root child counts "
                            + "are one and two, so these are different complete height-one trees.")),
                    Paragraph(Text(
                        "The periodic-core equivalence intertwines the induced periodic maps, "
                            + "and the canonical backward-path equivalence has the stated "
                            + "coordinate-zero computation. No relabeling can conjugate the "
                            + "maps because Fin 2 and Fin 3 have different cardinalities.")),
                    Paragraph(Text(
                        "Repository search found exact canonical periodic-core/path results but "
                            + "no transient-child or branch-completion primitive. Pinned Mathlib "
                            + "supplied periodic-point membership and finite-cardinality support, "
                            + "but no theorem combining the path equivalence and countermodel."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
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

    private static Formula Fin(byte size) => Apply(F.Id("Fin"), D(size));

    private static Formula Periodic(Formula update, Formula point) =>
        Apply(F.Id("Periodic"), update, point);

    private static Formula Child(Formula update, Formula parent) =>
        Apply(F.Id("TransientChild"), update, parent);

    private static Formula Card(Formula carrier) =>
        Apply(Seq(Operatorname, Grp(F.Id("card"))), carrier);

    private static Formula CoordinateZero(Formula orbit) =>
        Apply(Seq(F.Id("p"), Underscore, D(0)), orbit);

    private static Formula NoncommutationFormula()
    {
        Formula tau = F.Id("tau");
        Formula sigma = F.Id("sigma");
        Formula coreEquiv = F.Id("e");
        Formula orbit = F.Id("x");
        Formula one = F.Id("oneBranchMap");
        Formula two = F.Id("twoBranchMap");
        Formula point = F.Id("p");
        Formula child = F.Id("c");
        Formula oneRootChildren = Child(one, D(0));
        Formula twoRootChildren = Child(two, D(0));
        Formula pathEquiv = Apply(F.Id("BackwardEquiv"), tau, sigma, coreEquiv);

        return Disp(Seq(
            Open, Forall, Sp, tau, Comma, Sp, sigma, Comma, Sp, coreEquiv,
            Comma, Sp, orbit, Comma, Esc,
            CoordinateZero(Apply(pathEquiv, orbit)), Sp, Eq, Sp,
            Apply(coreEquiv, CoordinateZero(orbit)), Close,
            Sp, Land, Sp, Nl,
            Open, Exists, Sp, child, InMacro, Sp, Fin(2), Comma, Sp,
            Neg, Sp, Periodic(one, child), Close, Sp, Land, Sp,
            Open, Exists, Sp, child, InMacro, Sp, Fin(3), Comma, Sp,
            Neg, Sp, Periodic(two, child), Close, Sp, Land, Sp, Nl,
            Open, Forall, Sp, point, Comma, Sp,
            Apply(F.Id("countermodelCoreEquiv"), Apply(one, point)), Sp, Eq, Sp,
            Apply(two, Apply(F.Id("countermodelCoreEquiv"), point)), Close,
            Sp, Land, Sp, Nl,
            Open, Forall, Sp, orbit, Comma, Sp,
            CoordinateZero(Apply(
                Apply(F.Id("BackwardEquiv"), one, two, F.Id("countermodelCoreEquiv")),
                orbit)), Sp, Eq, Sp,
            Apply(F.Id("countermodelCoreEquiv"), CoordinateZero(orbit)), Close,
            Sp, Land, Sp, Nl,
            Open, Forall, Sp, child, InMacro, Sp, Fin(2), Comma, Sp,
            Neg, Sp, Periodic(one, child), Sp, Rightarrow, Sp,
            Apply(F.Id("IsEmpty"), Child(one, child)), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, child, InMacro, Sp, Fin(3), Comma, Sp,
            Neg, Sp, Periodic(two, child), Sp, Rightarrow, Sp,
            Apply(F.Id("IsEmpty"), Child(two, child)), Close,
            Sp, Land, Sp, Nl,
            Card(oneRootChildren), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Card(twoRootChildren), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            Card(oneRootChildren), Sp, Neq, Sp, Card(twoRootChildren),
            Sp, Land, Sp, Nl,
            Neg, Exists, Sp, F.Id("u"), Colon, Sp,
            Fin(2), Sp, Equiv, Sp, Fin(3), Comma, Esc,
            Apply(Seq(Operatorname, Grp(F.Id("Semiconj"))), F.Id("u"), one, two), Dot));
    }
}
