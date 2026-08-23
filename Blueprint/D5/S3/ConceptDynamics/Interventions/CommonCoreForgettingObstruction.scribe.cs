using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class CommonCoreForgettingObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nontrivial safety-blame core prevents safety-preserving complete blame erasure.",
        H("Common Core Forgetting Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-core-relation"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction."
                        + "commonCoreRelation"),
                H("Common core relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The common core relation of two concept readouts is the join of their "
                            + "kernel setoids, the least equivalence relation containing both "
                            + "indistinguishability relations.")),
                    Paragraph(Text(
                        "The quotient by this relation is the greatest common coarsening in the "
                            + "canonical concept factorization order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("common-core-obstructs-complete-forgetting"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction."
                        + "common_core_obstructs_complete_forgetting"),
                H("Nontrivial common core obstructs complete forgetting"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Safety, blame, and future availability are independent concept readouts "
                            + "on the same source carrier. Refinement is the canonical frozen "
                            + "family factorization relation.")),
                    Paragraph(Text(
                        "A common core is trivial exactly when its kernel join is the top setoid, "
                            + "which identifies every pair of source states. Thus the public "
                            + "conclusion negates safety preservation and complete blame erasure "
                            + "as a simultaneous pair of clauses.")),
                    Paragraph(Text(
                        "A safety factor through the future readout makes the future kernel no "
                            + "larger than the safety kernel. Joining both with the blame kernel "
                            + "preserves this order, so a top future-blame core would force the "
                            + "safety-blame core to be top as well.")),
                    Paragraph(Text(
                        "The common core is constructed from the two source kernels before the "
                            + "impossibility claim; it is not defined by the theorem's target.")),
                    Paragraph(Text(
                        "Repository search found no exact obstruction theorem. The proof directly "
                            + "imports the canonical concept carrier and refinement relation and "
                            + "applies the pinned setoid complete-lattice operations."))),
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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula safetyType = Subscript(F.Id("B"), F.Id("S"));
        Formula blameType = Subscript(F.Id("B"), F.Id("B"));
        Formula futureType = Subscript(F.Id("B"), F.Id("F"));
        Formula safety = F.Id("S");
        Formula blame = F.Id("B");
        Formula future = F.Id("F");
        Formula top = F.Id("top");
        Formula safetyCore = Call("commonCoreRelation", safety, blame);
        Formula futureCore = Call("commonCoreRelation", future, blame);
        Formula types = Seq(
            stateType, Comma, Sp, safetyType, Comma, Sp, blameType, Comma, Sp,
            futureType, Colon, Sp, Operatorname, Grp(F.Id("Type")));
        Formula readouts = Seq(
            safety, Colon, Sp, Arrow(stateType, safetyType), Comma, Sp,
            blame, Colon, Sp, Arrow(stateType, blameType), Comma, Sp,
            future, Colon, Sp, Arrow(stateType, futureType));
        Formula simultaneousClauses = Seq(
            Call("Refines", safety, future), Sp, Land, Sp,
            futureCore, Sp, Eq, Sp, top);

        return Disp(Seq(
            Forall, Sp, types, Comma, RowBreak, Grp(),
            readouts, Comma, RowBreak, Grp(),
            safetyCore, Sp, Neq, Sp, top, Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Grp(simultaneousClauses), Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
