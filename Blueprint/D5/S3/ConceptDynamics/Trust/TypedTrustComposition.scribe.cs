using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Trust;

internal sealed class TypedTrustCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed trust composes along one report chain, is characterized by target constancy "
            + "on report fibers, and can fail when intermediate scopes do not match.",
        H("Typed Trust Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interfaces-align"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Trust/TypedTrustComposition.InterfacesAlign"),
                H("A report interface aligns with a target"),
                StatementSource.FromAuthor(InterfacesAlignFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A report interface aligns with a target exactly when the report never "
                            + "identifies two states that the target distinguishes. Equivalently, "
                            + "the target is constant on every fiber of the report."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typed-trust-composes-iff-interfaces-align"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Trust/TypedTrustComposition."
                        + "typed_trust_composes_iff_interfaces_align"),
                H("Typed trust composes exactly through aligned interfaces"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Refinement is transitive along a single typed report chain. If the "
                            + "intermediate report factors through the outer report and the target "
                            + "factors through the intermediate report, then the target factors "
                            + "through the outer report.")),
                    Paragraph(Text(
                        "For a nonempty target codomain, a target factors through a report exactly "
                            + "when it is constant on the report's fibers. The forward direction "
                            + "follows from applying the factor map; the reverse direction is the "
                            + "standard factorization-through-fibers criterion.")),
                    Paragraph(Text(
                        "The Boolean-pair witness takes the outer report to be the first projection, "
                            + "the richer report to be the identity, the intermediate scope to be "
                            + "the first projection, and the target to be the second projection. "
                            + "The target factors through the identity and the scope factors through "
                            + "the outer report, but the target does not factor through that report.")),
                    Paragraph(Text(
                        "The failure does not contradict transitivity: the two available refinement "
                            + "premises pass through different intermediate readouts. The states "
                            + "(false, false) and (false, true) have the same outer report while their "
                            + "target values differ, exposing the missing target-relevant distinction."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula InterfacesAlign(Formula report, Formula target) =>
        Call("InterfacesAlign", report, target);

    private static Formula InterfacesAlignFormula()
    {
        Formula stateType = F.Id("X");
        Formula reportType = F.Id("R");
        Formula targetType = F.Id("T");
        Formula report = F.Id("qR");
        Formula target = F.Id("qT");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula sameReport = Seq(
            Apply(report, first), Sp, Eq, Sp, Apply(report, second));
        Formula sameTarget = Seq(
            Apply(target, first), Sp, Eq, Sp, Apply(target, second));

        return Disp(Seq(
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, reportType, Comma, Sp, targetType), type),
            Comma, RowBreak, Grp(),
            Typed(report, Arrow(stateType, reportType)), Comma, Sp,
            Typed(target, Arrow(stateType, targetType)), Comma, RowBreak, Grp(),
            InterfacesAlign(report, target), Sp, Iff, Sp,
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, stateType, Comma, Sp,
            Grp(sameReport), Sp, Rightarrow, Sp, sameTarget, Dot));
    }

    private static Formula CompositionClaim()
    {
        Formula stateType = F.Id("X");
        Formula outerType = F.Id("C");
        Formula intermediateType = F.Id("B");
        Formula targetType = F.Id("T");
        Formula outerReport = F.Id("qC");
        Formula intermediateReport = F.Id("qB");
        Formula target = F.Id("qT");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula premises = Seq(
            Refines(intermediateReport, outerReport), Sp, Land, Sp,
            Refines(target, intermediateReport));

        return Seq(
            Forall, Sp,
            Typed(
                Seq(
                    stateType, Comma, Sp, outerType, Comma, Sp,
                    intermediateType, Comma, Sp, targetType),
                type),
            Comma, RowBreak, Grp(),
            Typed(outerReport, Arrow(stateType, outerType)), Comma, Sp,
            Typed(intermediateReport, Arrow(stateType, intermediateType)), Comma, Sp,
            Typed(target, Arrow(stateType, targetType)), Comma, RowBreak, Grp(),
            Grp(premises), Sp, Rightarrow, Sp, Refines(target, outerReport));
    }

    private static Formula AlignmentClaim()
    {
        Formula stateType = F.Id("X");
        Formula reportType = F.Id("R");
        Formula targetType = F.Id("T");
        Formula report = F.Id("qR");
        Formula target = F.Id("qT");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula equivalence = Seq(
            Refines(target, report), Sp, Iff, Sp, InterfacesAlign(report, target));

        return Seq(
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, reportType, Comma, Sp, targetType), type),
            Comma, RowBreak, Grp(),
            Typed(report, Arrow(stateType, reportType)), Comma, Sp,
            Typed(target, Arrow(stateType, targetType)), Comma, RowBreak, Grp(),
            Call("Nonempty", targetType), Sp, Rightarrow, Sp, Grp(equivalence));
    }

    private static Formula ScopeMismatchWitness()
    {
        Formula boolean = F.Id("Bool");
        Formula stateType = Seq(boolean, Sp, Times, Sp, boolean);
        Formula reportC = F.Id("qC");
        Formula reportB = F.Id("qB");
        Formula scope = F.Id("scope");
        Formula target = F.Id("target");
        Formula booleanReadout = Arrow(stateType, boolean);

        return Seq(
            Exists, Sp, Typed(reportC, booleanReadout), Comma, RowBreak, Grp(),
            Typed(reportB, Arrow(stateType, stateType)), Comma, RowBreak, Grp(),
            Typed(Seq(scope, Comma, Sp, target), booleanReadout), Comma, RowBreak, Grp(),
            Refines(target, reportB), Sp, Land, Sp,
            Refines(scope, reportC), Sp, Land, Sp,
            Neg, Sp, Refines(target, reportC));
    }

    private static Formula TheoremFormula() =>
        Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Grp(CompositionClaim()), Sp, Land, RowBreak, Grp(),
            Grp(AlignmentClaim()), Sp, Land, RowBreak, Grp(),
            ScopeMismatchWitness(), Dot,
            End, Grp(F.Id("gathered"))));
}
