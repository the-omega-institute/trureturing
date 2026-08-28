using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class TargetFamilyEssenceMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimally sufficient joint target becomes finer under family enlargement.",
        H("Target-Family Essence Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multi-target-essence-sufficiency-and-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementAlgebra/"
                        + "TargetFamilyEssenceMonotonicity."
                        + "multi_target_essence_sufficiency_and_monotonicity"),
                H("Joint target minimality and family monotonicity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source's canonical essence for a target family is the existing "
                            + "jointTarget. A readout decides it exactly when the readout decides "
                            + "every component target.")),
                    Paragraph(Text(
                        "The joint target decides each component and is coarsest among all "
                            + "simultaneously sufficient concepts. These clauses are supplied by "
                            + "the frozen dependent-family theorem.")),
                    Paragraph(Text(
                        "The public enlargement clause uses the named sumTarget construction. It "
                            + "adjoins an arbitrary dependent family, and restriction along the "
                            + "left injection proves that the enlarged essence refines the old one."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Comma, Sp]);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula indexType = F.Id("I");
        Formula readoutType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula targets = F.Id("T");
        Formula readout = F.Id("R");
        Formula index = F.Id("i");
        Formula candidateType = F.Id("D");
        Formula candidate = F.Id("q");
        Formula addedIndex = F.Id("J");
        Formula addedType = F.Id("Z");
        Formula additional = F.Id("A");
        Formula added = F.Id("j");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula joint = Call("jointTarget", targets);
        Formula component = Apply(targets, index);
        Formula allThroughReadout = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Refines(component, readout));
        Formula allThroughJoint = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Refines(component, joint));
        Formula allThroughCandidate = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Refines(component, candidate));
        Formula least = Seq(
            Forall, Sp, Typed(candidateType, type), Comma, Sp,
            Typed(candidate, Arrow(state, candidateType)), Comma, Sp,
            Open, allThroughCandidate, Close, Sp, Rightarrow, Sp,
            Refines(joint, candidate));
        Formula enlarged = Call("sumTarget", targets, additional);
        Formula monotonicity = Seq(
            Forall, Sp, Typed(addedIndex, type), Comma, Sp,
            Typed(addedType, Arrow(addedIndex, type)), Comma, Sp,
            Typed(additional, Seq(
                Forall, Sp, Typed(added, addedIndex), Comma, Sp,
                Arrow(state, Apply(addedType, added)))), Comma, Sp,
            Refines(joint, Call("jointTarget", enlarged)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(state, type), Comma, Sp,
                Typed(indexType, type), Comma, Sp, Typed(readoutType, type), Comma),
            Seq(
                Typed(targetType, Arrow(indexType, type)), Comma, Sp,
                Typed(targets, Seq(
                    Forall, Sp, Typed(index, indexType), Comma, Sp,
                    Arrow(state, Apply(targetType, index)))), Comma),
            Seq(Typed(readout, Arrow(state, readoutType)), Comma),
            Seq(
                Grp(), OpenBracket, Open, Open, allThroughReadout, Close,
                Sp, Iff, Sp, Refines(joint, readout), Close, Sp, Land),
            Seq(Open, allThroughJoint, Close, Sp, Land, Sp, least, CloseBracket, Sp, Land),
            Seq(Open, monotonicity, Close, Dot),
        ]));
    }
}
