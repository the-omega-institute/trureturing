using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Combinatorics;

internal sealed class DecoratedNecklaceInvariantDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Combinatorics/DecoratedNecklaceInvariant."
            + "decorated_necklace_invariant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic rotation classes retain word length and decoration multiplicity "
            + "without identifying reflections.",
        H("Decorated Necklace Invariants"),
        Blocks(Describe.Lean(
            DescribeId.Create("decorated-necklace-invariant"),
            DeclarationHandle.Create(Declaration),
            H("Rotation classes retain length and multiplicity but distinguish reflection"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A necklace is Mathlib's quotient of lists by cyclic rotation. The "
                        + "underlying setoid relates two words exactly when the second is a "
                        + "rotation of the first; this includes the empty word and rotations "
                        + "by amounts larger than the word length.")),
                Paragraph(Text(
                    "A rotation preserves both list length and the multiset of decorations. "
                        + "Mapping a multiset of component words into rotation classes therefore "
                        + "defines the system invariant, and rotating any one component leaves "
                        + "that multiset of necklaces unchanged.")),
                Paragraph(Text(
                    "The words 1,2,3; 2,3,1; and 3,1,2 represent the same necklace. By "
                        + "contrast, 1,3,2 is not a rotation of 1,2,3 even though the two words "
                        + "have equal decoration multisets. Thus multiplicity is an invariant "
                        + "of a necklace, not a complete classification of necklaces."))),
            DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Rotate(Formula word, Formula turns) =>
        Call("rotate", word, turns);

    private static Formula Necklace(Formula word) =>
        Call("necklace", word);

    private static Formula Decorations(Formula word) =>
        Call("multiset", word);

    private static Formula Word(params Formula[] entries) =>
        Call("list", entries);

    private static Formula TheoremFormula()
    {
        Formula alpha = F.Id("alpha");
        Formula first = F.Id("u");
        Formula second = F.Id("v");
        Formula turns = F.Id("n");
        Formula components = F.Id("W");
        Formula word = F.Id("w");
        Formula listAlpha = Call("List", alpha);
        Formula word123 = Word(D(1), D(2), D(3));
        Formula word231 = Word(D(2), D(3), D(1));
        Formula word312 = Word(D(3), D(1), D(2));
        Formula word132 = Word(D(1), D(3), D(2));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, alpha, Colon, Sp, F.Id("Type"), Comma, Sp,
                first, Comma, Sp, second, Colon, Sp, listAlpha, Comma),
            Seq(
                Call("IsRotated", first, second), Sp, Leftrightarrow, Sp,
                Exists, Sp, turns, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                second, Sp, Eq, Sp, Rotate(first, turns), Comma),
            Seq(
                Call("IsRotated", first, second), Sp, Rightarrow, Sp,
                Open,
                Call("length", first), Sp, Eq, Sp, Call("length", second),
                Sp, Land, Sp,
                Decorations(first), Sp, Eq, Sp, Decorations(second),
                Close, Comma),
            Seq(
                Forall, Sp, components, Comma, Sp, word, Comma, Sp, turns, Comma, Sp,
                Call("systemNecklaces", Call("insert", Rotate(word, turns), components)),
                Sp, Eq, Sp,
                Call("systemNecklaces", Call("insert", word, components)), Comma),
            Seq(
                Necklace(word123), Sp, Eq, Sp, Necklace(word231), Sp, Eq, Sp,
                Necklace(word312), Comma),
            Seq(
                Necklace(word123), Sp, Neq, Sp, Necklace(word132), Sp, Land, Sp,
                Decorations(word123), Sp, Eq, Sp, Decorations(word132), Dot),
        ]));
    }
}
