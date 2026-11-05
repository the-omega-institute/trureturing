using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciNineBitObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AdmissibleWords/KBonacciNineBitObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two raw remainders of 1 + X cannot be acquired by one order-two legal "
            + "Boolean word using at most nine actual positions.",
        H("A simultaneous obstruction through nine bits"),
        Blocks(
            Paragraph(Text(
                "Work over ZMod 2. A word w of length n is a function from Fin n to Bool, "
                    + "read with position zero first, and P(w) is its original word polynomial: "
                    + "the coefficient of X^j is one exactly when w(j) is true. The predicate "
                    + "A(n,w) is DBonacciAdmissible 2 n w, the original scanner excluding two "
                    + "consecutive true bits. Every false bit counts toward n, and n may be zero.")),
            Paragraph(Text(
                "Let r_a(P) be the raw monic remainder P modulo Phi_a, where Phi_a is X^a "
                    + "minus the sum of X^j for zero <= j < a. Both observations below read "
                    + "the same word. No tail or phase condition is imposed.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-nine-bit-short-realization-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed common short realization"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim asks for one length at most nine and one accepted word whose "
                        + "two raw remainders equal the corresponding remainders of 1 + X. "
                        + "Separate words for the two coordinates do not satisfy this claim."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kbonacci-nine-bit-short-realization-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("There is no common short realization"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a nine-position word, write b_j for its bit as an element of "
                            + "ZMod 2. Monic division yields the two coefficient rows "
                            + "b_0+b_2+b_3+b_5+b_6+b_8 and b_1+b_2+b_4+b_5+b_7+b_8 for "
                            + "Phi_2. The three rows for Phi_3 are b_0+b_3+b_4+b_7+b_8, "
                            + "b_1+b_3+b_5+b_7, and b_2+b_3+b_6+b_7. The target requires "
                            + "these five values to be 1, 1, 1, 1, and 0, respectively.")),
                    Paragraph(Text(
                        "Explicit quotient identities establish these remainder formulas for "
                            + "every nine-position word. A finite decision over all functions "
                            + "from Fin 9 to Bool then excludes the five equations together with "
                            + "acceptance by the original scanner. Appending a false bit preserves "
                            + "both the word polynomial and scanner acceptance, so any shorter "
                            + "realization would give an excluded nine-position realization.")),
                    Paragraph(Text(
                        "This exclusion gives the lower bound for the specified target. "
                            + "It does not assert attainment at ten, identify the whole common "
                            + "image, or establish an exact saturation threshold."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w");
        Formula target = Seq(D(1), Sp, Plus, Sp, F.Id("X"));
        Formula observed = Call("P", w);
        Formula equations = And(
            Equal(Call("r", D(2), observed), Call("r", D(2), target)),
            Equal(Call("r", D(3), observed), Call("r", D(3), target)));
        Formula legal = And(Call("A", n, w), equations);
        Formula wordType = new Formula.TypeArrow(Call("Fin", n), Named("Bool"));
        Formula word = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("w"), wordType, legal);
        Formula bound = new Formula.Relation(n, FormulaRelationOperator.LessThanOrEqual, D(9));
        Formula length = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("n"), Seq(Mathbb, Grp(F.Id("N"))), And(bound, word));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, length));
    }
}
