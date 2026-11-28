using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ResidueRings;

internal sealed class MesyanQuantaleClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ring has a quantale unit on its additive submonoids exactly when it has a ring unit or is a torsion ring with unital primary components.",
        H("Classification of additive-submonoid quantale units in rings"),
        Blocks(Describe.Lean(
            DescribeId.Create("mesyan-question-36-ring-classification"),
            DeclarationHandle.Create("D5/S3/Arith/ResidueRings/MesyanQuantaleClassification.product_unit_iff"),
            H("The ring classification in Mesyan's Question 36"),
            StatementSource.FromAuthor(ClassificationStatement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let R be an associative ring with no assumed identity or commutativity. "
                    + "In Definition 4, the product of two additive submonoids consists of sums of a positive finite number "
                    + "of ordered pairwise products. This is Mathlib's additive-submonoid multiplication. "
                    + "It contains zero through the one-term sum of the product of two zeros. "
                    + "The shared reference for Definition 4 and Question 36 is "),
                    Ref("D5/L/ArithUnits/mesyan2026quantales"), Text(".")),
                Paragraph(Text("The quantale has a two-sided identity precisely if R has a two-sided "
                    + "multiplicative identity or its additive group is torsion and each prime-primary component "
                    + "has a two-sided identity belonging to that component. The component for p consists of "
                    + "elements killed by some natural power of p, with inherited ring operations. "
                    + "The dot after a prime power denotes repeated addition. "
                    + "Zero serves as the identity in a zero component and in the zero ring. "
                    + "The formula uses positive additive order for torsion since infinite additive order is "
                    + "represented by zero. The classification concerns the ring case of Question 36.")),
                Paragraph(Text("Testing a quantale unit on cyclic additive submonoids shows that each "
                    + "multiplier acts by natural multiples and that each element has a fixing multiplier. "
                    + "An infinite-order fixed point forces the left action to be injective and idempotent, "
                    + "giving a left identity. An order-p fixed point forces injectivity on the p-primary "
                    + "component. There the action is a scalar coprime to p, which can be inverted using a "
                    + "power of p that kills the projected multiplier. Passing to the opposite ring gives "
                    + "the corresponding right identities, and the left and right identities coincide.")),
                Paragraph(Text("A ring identity gives a quantale unit by taking its natural multiples. "
                    + "For a torsion ring, the primary identities can be added over the finite primary "
                    + "support of each element to fix it on both sides. Products between distinct primary "
                    + "components vanish, and the Chinese remainder theorem expresses each such action as "
                    + "a natural multiple on every argument. The additive submonoid of multipliers whose "
                    + "left and right actions agree with a natural multiple on each argument is then a "
                    + "two-sided quantale unit."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("mesyan-2026-question-36-ring-classification"),
                ResolutionKind.Proved)))));

    private static Formula Parens(Formula body) => Seq(Open, body, Close);

    private static Formula Bind(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Open, F.Id(name), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula UnitLaws(Formula unit, Formula element) =>
        Seq(unit, Sp, Cdot, Sp, element, Sp, Eq, Sp, element, Sp, Land, Sp,
            element, Sp, Cdot, Sp, unit, Sp, Eq, Sp, element);

    private static Formula KilledByPrimePower(Formula element) =>
        Bind(Exists, "j", Seq(Mathbb, Grp(F.Id("N"))),
            Seq(F.Id("p"), Caret, Grp(F.Id("j")), Sp, Cdot, Sp, element, Sp, Eq, Sp, D(0)));

    private static Formula ClassificationStatement()
    {
        Formula ring = F.Id("R");
        Formula submonoids = Seq(F.Id("AddSubmonoid"), Sp, ring);
        Formula unit = F.Id("u");
        Formula element = F.Id("x");
        Formula quantaleUnit = Bind(Exists, "E", submonoids,
            Bind(Forall, "M", submonoids, UnitLaws(F.Id("E"), F.Id("M"))));
        Formula ringUnit = Bind(Exists, "u", ring,
            Bind(Forall, "x", ring, UnitLaws(unit, element)));
        Formula torsion = Bind(Forall, "a", ring,
            Seq(D(0), Sp, Lt, Sp, F.Id("addOrderOf"), Open, F.Id("a"), Close));
        Formula primaryUnits = Bind(Forall, "p", F.Id("Primes"),
            Bind(Exists, "u", ring, Seq(Parens(KilledByPrimePower(unit)), Sp, Land, Sp,
                Parens(Bind(Forall, "x", ring, Seq(Parens(KilledByPrimePower(element)),
                    Sp, Rightarrow, Sp, Parens(UnitLaws(unit, element))))))));
        Formula equivalence = Seq(Parens(quantaleUnit), Sp, Leftrightarrow, Sp,
            Parens(ringUnit), Sp, Lor, Sp, Parens(Seq(Parens(torsion), Sp, Land, Sp, Parens(primaryUnits))));
        return Disp(Bind(Forall, "R", F.Id("Type"), Seq(
            OpenBracket, F.Id("NonUnitalRing"), Sp, ring, CloseBracket, Comma, Sp, equivalence)));
    }
}
