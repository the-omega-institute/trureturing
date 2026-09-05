using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class FiniteCompatibleCrtDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite congruences glue exactly under pairwise gcd compatibility, uniquely modulo lcm.",
        H("Finite Compatible CRT"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-compatible-crt-gluing"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/PrimePowers/FiniteCompatibleCrt.finite_crt_gluing"),
            H("Finite CRT gluing and integer representatives"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The index type I is finite, m assigns natural moduli, and a assigns "
                        + "integer representatives of the local data. P is the product of all "
                        + "m(i), L is their finite least common multiple, and pi(i,z) is the "
                        + "canonical ZMod castHom from modulus P to modulus m(i). The right "
                        + "side a(i) of the first equality is cast into ZMod(m(i)).")),
                Paragraph(Text(
                    "ModEq(n,x,y) means integer congruence modulo n. The middle clause "
                        + "identifies the entire solution set with one congruence class modulo "
                        + "L; setting y=x also supplies a simultaneous solution. Empty index "
                        + "types are included, with P=L=1. Zero moduli are allowed in the "
                        + "first two clauses; ZMod(0) records the whole integer.")),
                Paragraph(Text(
                    "The last clause assumes nonzero natural moduli, hence positive moduli. "
                        + "Adding P gives a distinct integer with the same finite residue data. "
                        + "Selecting an ordinary integer therefore requires additional "
                        + "restrictions such as a suitable bounded interval; sign alone is "
                        + "not asserted to suffice.")),
                Paragraph(Text(
                    "The proof imports the frozen binary compatible-residue image theorem. "
                        + "Finite induction derives compatibility between a merged solution "
                        + "and the next residue across gcd(L,m(j)), using gcd distribution "
                        + "over finite lcm, and then applies binary gluing. The coprime "
                        + "clause uses pinned Mathlib's ZMod.prodEquivPi."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
                items.Add(Seq(Comma, Sp));
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Par(Formula formula) => Seq(Open, formula, Close);

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);

    private static Formula MainFormula()
    {
        Formula index = F.Id("I");
        Formula m = F.Id("m");
        Formula a = F.Id("a");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula mi = At(m, i);
        Formula mj = At(m, j);
        Formula ai = At(a, i);
        Formula aj = At(a, j);
        Formula product = Seq(Prod, Underscore, Grp(i, Sp, InMacro, Sp, index), Sp, mi);
        Formula lcm = Seq(Operatorname, Grp(F.Id("lcm")), Underscore,
            Grp(i, Sp, InMacro, Sp, index), Sp, mi);
        Formula coprime = All(i, index, All(j, index, Seq(
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp, Call("Coprime", mi, mj))));
        Formula unique = Seq(Exists, Bang, Sp, z, Colon, Sp,
            Call("ZMod", product), Comma, Sp,
            All(i, index, Seq(Call("pi", i, z), Sp, Eq, Sp, ai)));
        Formula overlaps = All(i, index, All(j, index,
            Call("ModEq", Call("gcd", mi, mj), ai, aj)));
        Formula solutions = Seq(Exists, Sp, x, Colon, Sp, integers, Comma, Sp,
            All(y, integers, Par(Seq(
                Par(All(i, index, Call("ModEq", mi, y, ai))), Sp, Iff, Sp,
                Call("ModEq", lcm, y, x)))));
        Formula positive = All(i, index, Seq(mi, Sp, Neq, Sp, D(0)));
        Formula nonunique = All(x, integers, Seq(
            Exists, Sp, y, Colon, Sp, integers, Comma, Sp,
            y, Sp, Neq, Sp, x, Sp, Land, Sp,
            Par(All(i, index, Call("ModEq", mi, y, x)))));
        return Disp(Seq(
            Forall, Sp, index, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("Fintype", index), CloseBracket, Comma, Sp,
            m, Colon, Sp, new Formula.TypeArrow(index, naturals), Comma, Sp,
            a, Colon, Sp, new Formula.TypeArrow(index, integers), Comma, Sp,
            Par(Seq(Par(coprime), Sp, Rightarrow, Sp, unique)), Sp, Land, Sp,
            Par(Seq(Par(overlaps), Sp, Iff, Sp, Par(solutions))), Sp, Land, Sp,
            Par(Seq(Par(positive), Sp, Rightarrow, Sp, nonunique)), Dot));
    }
}
