using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class FibonacciAuxiliaryModNineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/FibonacciAuxiliaryModNine.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The modulo-nine square of the original Fibonacci value is controlled by "
            + "a multiplicative character of its index modulo twelve.",
        H("An Auxiliary Modulo-Nine Fibonacci Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("auxiliary-character-twelve"),
                DeclarationHandle.Create(Prefix + "auxiliaryCharacter12"),
                H("The explicit index character"),
                StatementSource.FromAuthor(CharacterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each natural n, the integer-valued character is one when "
                        + "n modulo twelve is one or eleven, minus one when it is "
                        + "five or seven, and zero otherwise. It is an auxiliary "
                        + "readout; the Fibonacci sequence and its golden field "
                        + "have not been replaced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("auxiliary-character-multiplicative"),
                DeclarationHandle.Create(Prefix + "auxiliary_character_mul"),
                H("Multiplicativity including zero values"),
                StatementSource.FromAuthor(MultiplicativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every two natural numbers m,n, the character of their "
                        + "product equals the product of their characters. The "
                        + "proof reduces the universal assertion to all twelve "
                        + "residue classes in both arguments. There is no "
                        + "coprimality hypothesis in this declaration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-square-mod-nine"),
                DeclarationHandle.Create(Prefix + "fibonacci_square_mod_nine"),
                H("The actual Fibonacci square for every eligible index"),
                StatementSource.FromAuthor(SquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural n whose residue modulo six is one or "
                        + "five, the equality F_n^2=4-3*eta(n) holds in ZMod 9. "
                        + "The recurrence first proves period twenty-four for "
                        + "all indices and then proves reduction to that finite "
                        + "period. A complete table finishes the universal "
                        + "congruence. The later integer Fermat-quotient and "
                        + "primitive-factor weighted identities are ordinary "
                        + "proofs in the WSS dossier, not extra conclusions of "
                        + "this declaration."))),
                DescribeRole.Theorem))));

    private static Formula V(string n) => F.Id(n);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] xs)
    {
        var terms = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) { terms.Add(Comma); terms.Add(Sp); }
            terms.Add(xs[i]);
        }
        terms.Add(Close);
        return Seq([.. terms]);
    }
    private static Formula All(string n, Formula body) =>
        Seq(Forall, Sp, V(n), Sp, InMacro, Sp, NatType(), Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Eta(Formula n) => Call("auxiliaryCharacter12", n);
    private static Formula Rem(Formula n, string d) => Call("Nat.mod", n, V(d));
    private static Formula CharacterFormula()
    {
        var first = Call("Or", Eqn(Rem(V("n"), "12"), V("1")),
            Eqn(Rem(V("n"), "12"), V("11")));
        var second = Call("Or", Eqn(Rem(V("n"), "12"), V("5")),
            Eqn(Rem(V("n"), "12"), V("7")));
        return Disp(All("n", Eqn(Eta(V("n")), Call("ite", first, V("1"),
            Call("ite", second, Call("neg", V("1")), V("0"))))));
    }
    private static Formula MultiplicativeFormula() => Disp(All("m", All("n",
        Eqn(Eta(Call("mul", V("m"), V("n"))), Call("mul", Eta(V("m")), Eta(V("n")))))));
    private static Formula SquareFormula()
    {
        var hypothesis = Call("Or", Eqn(Rem(V("n"), "6"), V("1")),
            Eqn(Rem(V("n"), "6"), V("5")));
        var left = new Formula.Power(Call("castToZMod", V("9"), Call("Nat.fib", V("n"))), V("2"));
        var right = Call("sub", Call("castToZMod", V("9"), V("4")),
            Call("mul", Call("castToZMod", V("9"), V("3")),
                Call("castToZMod", V("9"), Eta(V("n")))));
        return Disp(All("n", Call("Implies", hypothesis, Eqn(left, right))));
    }
}
