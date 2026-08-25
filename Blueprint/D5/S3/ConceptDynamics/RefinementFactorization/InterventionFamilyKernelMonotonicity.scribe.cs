using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class InterventionFamilyKernelMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enlarging an arbitrary intervention family shrinks its joint-law equality kernel.",
        H("Intervention-Family Kernel Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("intervention-family-kernel-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementFactorization/"
                        + "InterventionFamilyKernelMonotonicity."
                        + "intervention_family_kernel_monotonicity"),
                H("More interventions can only shrink the causal residual"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each intervention supplies a law-valued readout on the common model "
                            + "carrier. For any allowed family, the canonical joint readout "
                            + "constructs its complete interventional law profile.")),
                    Paragraph(Text(
                        "When family A is contained in family B, restricting a B-profile to A "
                            + "recovers the A-profile coordinate by coordinate. Equality of two "
                            + "B-profiles therefore implies equality of their A-profiles.")),
                    Paragraph(Text(
                        "The public theorem quantifies arbitrary set-indexed families. The "
                            + "existing finite-index theorem is a genuine special case and is not "
                            + "used as coverage for this unrestricted source claim.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no arbitrary-family theorem. "
                            + "The proof evaluates equality of the larger canonical joint readout "
                            + "at each included intervention."))),
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
        Formula intervention = F.Id("I");
        Formula model = F.Id("M");
        Formula lawValue = F.Id("L");
        Formula law = F.Id("law");
        Formula familyA = F.Id("A");
        Formula familyB = F.Id("B");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula restrictedA = Call("restrict", law, familyA);
        Formula restrictedB = Call("restrict", law, familyB);
        Formula profileA = Call("jointReadout", restrictedA);
        Formula profileB = Call("jointReadout", restrictedB);

        return Disp(Seq(
            Forall, Sp, intervention, Comma, Sp, model, Comma, Sp,
            lawValue, Colon, Sp, type, Comma, RowBreak, Grp(),
            law, Colon, Sp, intervention, Sp, To, Sp, model, Sp, To, Sp,
            lawValue, Comma, Sp,
            familyA, Comma, Sp, familyB, Colon, Sp, Call("Set", intervention),
            Comma, RowBreak, Grp(),
            familyA, Sp, Subseteq, Sp, familyB, RowBreak, Grp(),
            Rightarrow, Sp,
            Call("ker", profileB), Sp, Subseteq, Sp, Call("ker", profileA), Dot));
    }
}
