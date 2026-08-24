using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class DeterministicInterfaceEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six deterministic interface criteria are equivalent on the realized readout image.",
        H("Deterministic Interface Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-interface-sixfold-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence."
                        + "deterministic_interface_sixfold_equivalence"),
                H("Six interface criteria are equivalent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a state type X, interface type B, readout q, and deterministic "
                            + "update F, the theorem compares six descriptions of the same "
                            + "interface behavior. Effective descent asks for a unique update "
                            + "on the realized readout image, while interface congruence says "
                            + "that F preserves every q-fiber.")),
                    Paragraph(Text(
                        "The remaining four entries express the same condition in different "
                            + "languages: no pair of equal-readout states is a carry witness, "
                            + "the composite q after F factors through q, every proposition "
                            + "constant on q-fibers remains so after F, and the depth-zero and "
                            + "depth-one kernels coincide.")),
                    Paragraph(Text(
                        "The equivalence is proved on the realized image of q and uses no "
                            + "finiteness hypothesis. The factorization and kernel arguments "
                            + "also make explicit why one-step interface equality already "
                            + "captures the full deterministic descent criterion."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        DefinitionDsl.Call(name, arguments);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula interfaceType = F.Id("B");
        Formula readout = F.Id("q");
        Formula update = F.Id("F");
        Formula left = F.Id("x");
        Formula right = F.Id("y");

        Formula effectiveDescent = Call("EffectiveDescent", readout, update);
        Formula congruence = Call("InterfaceCongruence", readout, update);
        Formula carry = Call(
            "IsCarryWitness", readout, update, readout, left, right);
        Formula noCarry = Seq(
            Forall, Sp, left, Comma, Sp, right, InMacro, Sp, stateType,
            Comma, Sp, Neg, Sp, carry);
        Formula composite = Seq(readout, Sp, Circ, Sp, update);
        Formula factorsThrough = Call("FactorsThrough", composite, readout);
        Formula pullbackInvariant = Call("PullbackInvariant", readout, update);
        Formula zeroKernel = Call("depthZeroKernel", readout);
        Formula oneKernel = Call("depthOneKernel", readout, update);
        Formula kernelEquality = Seq(zeroKernel, Sp, Eq, Sp, oneKernel);
        Formula sixConditions = Grp(
            OpenBracket,
            effectiveDescent, Comma, Sp,
            congruence, Comma, Sp,
            noCarry, Comma, Sp,
            factorsThrough, Comma, Sp,
            pullbackInvariant, Comma, Sp,
            kernelEquality,
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, interfaceType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, stateType, Sp, To, Sp, interfaceType, Comma, Sp,
            update, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma,
            RowBreak, Grp(),
            Call("ListTFAE", sixConditions), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
