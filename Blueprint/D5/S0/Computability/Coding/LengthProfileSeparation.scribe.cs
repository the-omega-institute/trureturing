using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class LengthProfileSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal codeword lengths and equal Kraft mass do not control immutable extension depth.",
        H("Length-Profile Separation for Immutable Prefix Codes"),
        Blocks(
            Paragraph(Text(
                "For arbitrary d and positive r, the spread family appends r zeroes to every "
                    + "d-bit word, while the packed family prepends the same zero block. Both "
                    + "families are prefix-free and have exactly the same complete multiset of "
                    + "codeword lengths.")),
            Paragraph(Text(
                "The parameters d, r, and every queried depth n are natural numbers, and all "
                    + "words are lists over Fin 2. The displayed mass is a real sum. The val/map "
                    + "expressions retain multiplicity in the full multiset of lengths; "
                    + "Nonempty(freeAt(C,n)) means that a length-n word is incomparable in both "
                    + "prefix directions with every existing word of C.")),
            Describe.Lean(
                DescribeId.Create("equal-lengths-unbounded-extension-gap"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/LengthProfileSeparation.equal_lengths_unbounded_extension_gap"),
                H("Equal length profiles hide an unbounded extension gap"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The spread code has Kraft mass (1/2)^r. Equality of the complete length "
                            + "multisets therefore gives the packed code the same mass, although "
                            + "the Lean conjunction records the spread mass explicitly.")),
                    Paragraph(Text(
                        "At depth n the spread family has a compatible slot exactly when d < n, "
                            + "whereas the packed family has one exactly when 0 < n. Their shortest "
                            + "possible immutable extension lengths are consequently d + 1 and 1, "
                            + "so fixing positive r and increasing d makes the gap unbounded."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/ImmutableExtension"))]));

    private static Formula SeparationFormula()
    {
        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula n = F.Id("n");
        Formula w = F.Id("w");
        Formula spread = Call("spreadCode", d, r);
        Formula packed = Call("packedCode", d, r);

        Formula spreadPrefixFree = Call("IsPrefixFree", spread);
        Formula packedPrefixFree = Call("IsPrefixFree", packed);
        Formula equalLengths = F.Seq(
            Call("map", Call("val", spread), F.Id("length")), Sp, Eq, Sp,
            Call("map", Call("val", packed), F.Id("length")));
        Formula spreadMass = F.Seq(
            Sum, Underscore, Grp(w, Sp, InMacro, Sp, spread), Sp,
            new Formula.Power(
                Grp(D(1), Sp, Slash, Sp, D(2)),
                Call("length", w)),
            Sp, Eq, Sp,
            new Formula.Power(Grp(D(1), Sp, Slash, Sp, D(2)), r));
        Formula spreadThreshold = F.Seq(
            Forall, Sp, n, Comma, Sp,
            Call("Nonempty", Call("freeAt", spread, n)), Sp,
            Leftrightarrow, Sp, d, Sp, Lt, Sp, n);
        Formula packedThreshold = F.Seq(
            Forall, Sp, n, Comma, Sp,
            Call("Nonempty", Call("freeAt", packed, n)), Sp,
            Leftrightarrow, Sp, D(0), Sp, Lt, Sp, n);

        Formula conclusion = And(
            spreadPrefixFree,
            packedPrefixFree,
            equalLengths,
            spreadMass,
            spreadThreshold,
            packedThreshold);

        return Disp(F.Seq(
            Forall, Sp, d, Comma, Sp, r, Comma, Sp,
            D(0), Sp, Lt, Sp, r, Sp, Rightarrow, Sp,
            conclusion, Dot));
    }

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula item in rest)
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        return result;
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
