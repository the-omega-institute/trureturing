using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class ComplementFiberLiftDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Negation/ComplementFiberLift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A section lifts base complement, and the lift square is its fiber retraction.",
        H("Complement Fiber Lift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-section-lifts-base-complement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "sectionLift_isComplementLift"),
                H("A right-inverse section lifts base complement"),
                StatementSource.FromAuthor(LiftFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The section lift first reads the base value, applies the supplied base "
                            + "negation, and then chooses the section representative over that "
                            + "negated value.")),
                    Paragraph(Text(
                        "The right-inverse hypothesis projects this representative back to the "
                            + "negated base value. This is exactly the pointwise complement-lift "
                            + "condition, with no injectivity requirement on the section."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-lift-square-is-the-section-retraction"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "sectionLift_square"),
                H("The lift square is the section retraction"),
                StatementSource.FromAuthor(SquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "After the first lift, the right-inverse section exposes the complemented "
                            + "base value. Applying the lift again invokes base negation a second "
                            + "time.")),
                    Paragraph(Text(
                        "Base involutivity cancels those two negations. The square of the lift is "
                            + "therefore not asserted to be the identity on all of the total "
                            + "space; it is exactly the retraction that sends each point to its "
                            + "chosen section representative."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Lift(Formula q, Formula negation, Formula section) =>
        Call("sectionLift", q, negation, section);

    private static Formula BinderPrefix(
        Formula q,
        Formula baseNegation,
        Formula section) =>
        Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Q")), Comma, Sp,
            baseNegation, Colon, Sp, Arrow(F.Id("Q"), F.Id("Q")), Comma,
            RowBreak, Grp(),
            section, Colon, Sp, Arrow(F.Id("Q"), F.Id("X")), Comma, Sp);

    private static Formula LiftFormula()
    {
        Formula q = F.Id("q");
        Formula baseNegation = F.Id("baseNegation");
        Formula section = F.Id("sect");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            BinderPrefix(q, baseNegation, section),
            Call("RightInverse", section, q), Sp, Rightarrow, RowBreak, Grp(),
            Call("IsComplementLift", q, baseNegation,
                Lift(q, baseNegation, section)),
            Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula SquareFormula()
    {
        Formula q = F.Id("q");
        Formula baseNegation = F.Id("baseNegation");
        Formula section = F.Id("sect");
        Formula lift = Lift(q, baseNegation, section);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            BinderPrefix(q, baseNegation, section),
            Open,
            Call("RightInverse", section, q), Sp, Land, Sp,
            Call("Involutive", baseNegation),
            Close, Sp, Rightarrow, RowBreak, Grp(),
            lift, Sp, Circ, Sp, lift, Sp, Eq, Sp,
            section, Sp, Circ, Sp, q, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
