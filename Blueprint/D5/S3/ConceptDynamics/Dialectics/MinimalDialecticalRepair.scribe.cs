using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class MinimalDialecticalRepairDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Dialectics/MinimalDialecticalRepair.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit carry forces the least target-complete refinement of a current concept.",
        H("Minimal Dialectical Repair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("carry-witness"),
                DeclarationHandle.Create(DeclarationPrefix + "IsCarryWitness"),
                H("Explicit carry witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A carry witness consists of two states with equal current readouts and "
                        + "unequal target readouts after the process. It is a concrete "
                        + "counterexample to current target-closure, not a contradictory proposition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("minimal-dialectical-repair"),
                DeclarationHandle.Create(DeclarationPrefix + "minimal_dialectical_repair"),
                H("Least target-complete repair"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The current concept, process, and target are independent source primitives. "
                            + "Their repair is constructed directly as the joint readout of the "
                            + "current value and the target consequence.")),
                    Paragraph(Text(
                        "The first two public conjuncts preserve every current distinction and make "
                            + "the target consequence decidable. The third is the universal "
                            + "minimality property among all readouts with those two refinements.")),
                    Paragraph(Text(
                        "The final public conjunct states the negative step: any explicit carry "
                            + "witness refutes factorization of the target consequence through the "
                            + "current readout. The canonical concept-join theorem supplies the "
                            + "three positive clauses directly."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula currentType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula candidateType = F.Id("D");
        Formula current = F.Id("C");
        Formula process = F.Id("F");
        Formula target = F.Id("K");
        Formula candidate = F.Id("Q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula consequence = Seq(target, Sp, Circ, Sp, process);
        Formula repair = Call("conceptJoin", current, Grp(consequence));
        Formula preserves = Call("Refines", current, repair);
        Formula decides = Call("Refines", Grp(consequence), repair);
        Formula candidatePreserves = Call("Refines", current, candidate);
        Formula candidateDecides = Call("Refines", Grp(consequence), candidate);
        Formula least = Call("Refines", repair, candidate);
        Formula carry = Call("IsCarryWitness", current, process, target, left, right);
        Formula currentClosed = Call("Refines", Grp(consequence), current);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, currentType, Comma, Sp, targetType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            current, Colon, Sp, Arrow(stateType, currentType), Comma, Sp,
            process, Colon, Sp, Arrow(stateType, stateType), Comma, Sp,
            target, Colon, Sp, Arrow(stateType, targetType), Comma, RowBreak, Grp(),
            preserves, Sp, Land, RowBreak, Grp(),
            decides, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, candidateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            candidate, Colon, Sp, Arrow(stateType, candidateType), Comma, Sp,
            candidatePreserves, Sp, Land, Sp, candidateDecides, Sp,
            Rightarrow, Sp, least, Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, left, Comma, Sp, right, InMacro, Sp, stateType,
            Comma, Sp, carry, Sp, Rightarrow, Sp, Neg, currentClosed, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
