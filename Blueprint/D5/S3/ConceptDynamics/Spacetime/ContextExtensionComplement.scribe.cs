using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class ContextExtensionComplementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite context embedding transports complements with an explicit new-region charge defect.",
        H("Context Extension and Complement Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("context-extension-complement-full-spec"),
                DeclarationHandle.Create(Prefix + "context_extension_complement_spec"),
                H("The complete extension and complement proposition"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite context embedding and an old selection, let R be the "
                            + "new current region. The kernel-checked conjunction records all "
                            + "three displayed transport identities together with disjointness, "
                            + "the exactness criterion, the zero-charge readout criterion, and "
                            + "the balanced-context consequence.")),
                    Paragraph(Text(
                        "The individual declarations below expose each component for downstream "
                            + "use; the conjunction records the proposition's complete algebraic "
                            + "content."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-map-readout"),
                DeclarationHandle.Create(Prefix + "map_readout"),
                H("Transport preserves the selected readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An attribute-preserving archive embedding maps every old current selection into the "
                        + "new current region. The signed finite sum is unchanged by this transport, so q "
                        + "of the mapped history equals q of the original history."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-q-map"),
                DeclarationHandle.Create(Prefix + "q_map"),
                H("Transport preserves q"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The q-valued form is the same transported readout identity after packaging the context "
                        + "and selection pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-decomposition"),
                DeclarationHandle.Create(Prefix + "complement_decomposition"),
                H("The transported complement splits exactly"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The complement of a mapped selection in the larger current region is the disjoint "
                        + "union of the mapped old complement and the genuinely new current events. This "
                        + "finite set identity accounts for every event and uses the embedding's current "
                        + "region containment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-disjoint-new-region"),
                DeclarationHandle.Create(Prefix + "complement_map_disjoint_newRegion"),
                H("The two complement pieces are disjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mapped old complement and the new current region cannot share an event: membership "
                        + "in the latter excludes membership in the mapped old current region."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-charge-difference"),
                DeclarationHandle.Create(Prefix + "complement_charge_difference"),
                H("The complement readout defect is exactly new-region charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtracting the old complement readout from the transported complement readout "
                        + "cancels the mapped old events. The only remaining contribution is the signed "
                        + "charge of the new current region."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-q-charge-difference"),
                DeclarationHandle.Create(Prefix + "q_complement_charge_difference"),
                H("The q complement defect is exactly new-region charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The q-valued form packages the same complement difference and therefore has the same "
                        + "new-region charge defect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-exact-iff"),
                DeclarationHandle.Create(Prefix + "complement_decomposition_exact_iff"),
                H("Exact complement transport is equivalent to no new region"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set decomposition reduces to literal equality with the mapped old complement "
                        + "precisely when the new current region is empty. This is an exact finite iff, "
                        + "separate from the weaker possibility of charge cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-readout-iff"),
                DeclarationHandle.Create(Prefix + "q_complement_readout_exchange_iff"),
                H("Complement readouts agree exactly when the defect balances"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerical complement readouts are equal exactly when the new current region has "
                        + "zero signed charge. Thus a nonempty extension can still be invisible to q when its "
                        + "positive and negative contributions balance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-underlying-readout-iff"),
                DeclarationHandle.Create(Prefix + "complement_readout_exchange_iff"),
                H("Underlying complement readouts agree exactly when the defect balances"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same defect criterion holds for the underlying signed readout: equality of the "
                        + "two complement readouts is equivalent to zero charge in the new region."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("context-extension-complement-balanced-charge"),
                DeclarationHandle.Create(Prefix + "balanced_newRegion_charge_zero"),
                H("Balanced contexts make the extension charge vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If both source and target contexts are balanced, the target background charge splits "
                        + "between the transported source current region and the new region. Since transport "
                        + "preserves the source charge and both backgrounds are zero, the new region has zero "
                        + "signed charge. Exact set equality can still fail when that region is nonempty."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/ComplementCharge"))
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula SetDifference(Formula left, Formula right) =>
        Seq(left, Sp, Setminus, Sp, right);

    private static Formula Q(Formula context, Formula value) =>
        Call("q", context, value);

    private static Formula Charge(Formula context, Formula region) =>
        Call("charge", context, region);

    private static Formula Complement(Formula context, Formula value) =>
        Call("complement", context, value);

    private static Formula TheoremFormula()
    {
        Formula c = F.Id("C"), d = F.Id("D"), selection = F.Id("A");
        Formula omegaC = F.Id("OmegaC"), omegaD = F.Id("OmegaD");
        Formula mappedSelection = Call("j", selection);
        Formula mappedCurrent = Call("j", omegaC);
        Formula oldComplement = SetDifference(omegaC, selection);
        Formula mappedOldComplement = Call("j", oldComplement);
        Formula newRegion = F.Id("R");
        Formula targetComplement = SetDifference(omegaD, mappedSelection);
        Formula oldReadout = Complement(c, selection);
        Formula targetReadout = Complement(d, mappedSelection);
        Formula chargeDefect = Charge(d, newRegion);
        Formula transport = Equal(Q(d, mappedSelection), Q(c, selection));
        Formula split = Equal(targetComplement,
            Seq(mappedOldComplement, Sp, Operatorname, Grp(F.Id("union")), Sp, newRegion));
        Formula disjoint = Call("Disjoint", mappedOldComplement, newRegion);
        Formula difference = Equal(
            new Formula.Binary(Q(d, targetReadout), FormulaBinaryOperator.Subtract,
                Q(c, oldReadout)), chargeDefect);
        Formula exact = Iff(Equal(targetComplement, mappedOldComplement),
            Equal(newRegion, Emptyset));
        Formula readout = Iff(Equal(Q(d, targetReadout), Q(c, oldReadout)),
            Equal(chargeDefect, D(0)));
        Formula balanced = Implies(
            And(Call("Balanced", c), Call("Balanced", d)), Equal(chargeDefect, D(0)));
        Formula body = And(transport,
            And(split,
                And(disjoint,
                    And(difference,
                        And(exact, And(readout, balanced))))));
        return Disp(Seq(
            F.Id("R"), Sp, FormulaDsl.Eq, Sp, SetDifference(omegaD, mappedCurrent), Comma, Sp, body, Dot));
    }
}
