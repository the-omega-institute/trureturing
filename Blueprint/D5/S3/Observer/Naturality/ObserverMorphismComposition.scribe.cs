using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Naturality;

internal sealed class ObserverMorphismCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evaluation-preserving observer morphisms compose in the state and protocol directions.",
        H("Observer Morphism Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-morphism-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Naturality/ObserverMorphismComposition."
                        + "observer_morphism_composition"),
                H("Observer morphism composition"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Three observers share one law carrier. Each observer has its own state "
                            + "and protocol carriers and an evaluation map into that law carrier.")),
                    Paragraph(Text(
                        "The first morphism translates states from the first observer to the "
                            + "second and compiles protocols in the reverse direction. The second "
                            + "morphism does the same from the second observer to the third. Both "
                            + "pairs preserve evaluation.")),
                    Paragraph(Text(
                        "Their state maps compose forward, while their protocol maps compose in "
                            + "the opposite order. Substituting the two preservation equalities "
                            + "proves that this composite pair again preserves evaluation.")),
                    Paragraph(Text(
                        "Repository searches found no canonical observer-morphism structure or "
                            + "exact theorem to reuse. The proof applies the pinned library's "
                            + "function-composition computation rule and the two stated premises."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(string name, byte index) =>
        Seq(F.Id(name), Underscore, Grp(D(index)));

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula EvaluationLaw(
        Formula targetEvaluation,
        Formula sourceEvaluation,
        Formula stateMap,
        Formula protocolMap,
        Formula sourceState,
        Formula targetProtocol) =>
        Seq(
            Apply(targetEvaluation, Apply(stateMap, sourceState), targetProtocol),
            Sp, Eq, Sp,
            Apply(sourceEvaluation, sourceState, Apply(protocolMap, targetProtocol)));

    private static Formula StatementFormula()
    {
        Formula x1 = Subscript("X", 1);
        Formula x2 = Subscript("X", 2);
        Formula x3 = Subscript("X", 3);
        Formula p1 = Subscript("P", 1);
        Formula p2 = Subscript("P", 2);
        Formula p3 = Subscript("P", 3);
        Formula e1 = Subscript("e", 1);
        Formula e2 = Subscript("e", 2);
        Formula e3 = Subscript("e", 3);
        Formula f1 = Subscript("f", 1);
        Formula f2 = Subscript("f", 2);
        Formula g1 = Subscript("g", 1);
        Formula g2 = Subscript("g", 2);
        Formula state = F.Id("x");
        Formula protocol = F.Id("p");
        Formula law = F.Id("Law");
        Formula stateComposite = Seq(Open, f2, Sp, Circ, Sp, f1, Close);
        Formula protocolComposite = Seq(Open, g1, Sp, Circ, Sp, g2, Close);
        Formula firstLaw = Seq(
            Forall, Sp, state, Sp, InMacro, Sp, x1, Comma, Sp,
            Forall, Sp, protocol, Sp, InMacro, Sp, p2, Comma, Esc,
            EvaluationLaw(e2, e1, f1, g1, state, protocol));
        Formula secondLaw = Seq(
            Forall, Sp, state, Sp, InMacro, Sp, x2, Comma, Sp,
            Forall, Sp, protocol, Sp, InMacro, Sp, p3, Comma, Esc,
            EvaluationLaw(e3, e2, f2, g2, state, protocol));
        Formula compositeLaw = Seq(
            Forall, Sp, state, Sp, InMacro, Sp, x1, Comma, Sp,
            Forall, Sp, protocol, Sp, InMacro, Sp, p3, Comma, Esc,
            EvaluationLaw(e3, e1, stateComposite, protocolComposite, state, protocol));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, x1, Comma, Sp, x2, Comma, Sp, x3, Comma, Sp,
            p1, Comma, Sp, p2, Comma, Sp, p3, Comma, Sp, law, Colon, Sp,
            F.Id("Type"), Comma, RowBreak,
            Forall, Sp, e1, Colon, Sp, Arrow(x1, Arrow(p1, law)), Comma, Sp,
            e2, Colon, Sp, Arrow(x2, Arrow(p2, law)), Comma, Sp,
            e3, Colon, Sp, Arrow(x3, Arrow(p3, law)), Comma, RowBreak,
            Forall, Sp, f1, Colon, Sp, Arrow(x1, x2), Comma, Sp,
            g1, Colon, Sp, Arrow(p2, p1), Comma, Sp,
            f2, Colon, Sp, Arrow(x2, x3), Comma, Sp,
            g2, Colon, Sp, Arrow(p3, p2), Comma, RowBreak,
            Open, firstLaw, Close, Sp, Land, Sp,
            Open, secondLaw, Close, Sp, Rightarrow, RowBreak,
            compositeLaw, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
