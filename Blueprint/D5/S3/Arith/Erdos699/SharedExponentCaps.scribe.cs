using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Erdos699;

internal sealed class SharedExponentCapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact 11-23 shared-exponent residues and their four impossible lift rows.",
        H("Erdos 699 Shared Exponent Caps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos699-shared-exponent-residues"),
                DeclarationHandle.Create("D5/S3/Arith/Erdos699/SharedExponentCaps.prime_and_lift_residues"),
                H("Base-two residues and prime-power returns"),
                StatementSource.FromAuthor(ResidueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact numeral identities give the residues of 2 at the two endpoint "
                        + "primes, the first lift modulo 121, the return at exponent 110, and "
                        + "the prime periods modulo 11 and 23."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("erdos699-first-return"),
                DeclarationHandle.Create("D5/S3/Arith/Erdos699/SharedExponentCaps.first_return_mod_121"),
                H("No earlier multiple of ten returns modulo 121"),
                StatementSource.FromAuthor(FirstReturnFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive z below 11, the exponent 10z does not return 2 to "
                        + "one modulo 121."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("erdos699-shared-exponent-caps"),
                DeclarationHandle.Create("D5/S3/Arith/Erdos699/SharedExponentCaps.shared_lift_caps"),
                H("The four endpoint lift rows have empty intersections"),
                StatementSource.FromAuthor(CapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural exponent, each row excludes at least one of its two "
                        + "required residues. The four rows therefore cannot be realized by "
                        + "one common exponent."))),
                DescribeRole.Theorem))));

    private static Formula ResidueFormula()
    {
        Formula two = Num(2);
        Formula n11 = Num(11), n23 = Num(23), n121 = Num(121);
        return Disp(And(
            Eq(Mod(Pow(two, D(8)), n11), D(3)),
            Eq(Mod(Pow(two, D(8)), n23), D(3)),
            Eq(Mod(Pow(two, Num(10)), n121), Mod(Add(D(1), Mul(D(5), n11)), n121)),
            Eq(Mod(Pow(two, Num(110)), n121), D(1)),
            Eq(Mod(Pow(two, Num(10)), n11), D(1)),
            Eq(Mod(Pow(two, Num(11)), n23), D(1))));
    }

    private static Formula FirstReturnFormula()
    {
        Formula z = F.Id("z");
        Formula premise = And(
            Lt(D(0), z), Lt(z, Num(11)));
        Formula conclusion = Neq(Mod(Pow(D(2), Mul(Num(10), z)), Num(121)), D(1));
        return Disp(Forall("z", Nat(), Implies(premise, conclusion)));
    }

    private static Formula CapFormula()
    {
        Formula n = F.Id("N");
        Formula row(int lift, int endpoint) => new Formula.Logic(
            Neq(Mod(n, Num(110)), Num(lift)), FormulaLogicOperator.Or,
            Neq(Mod(n, Num(11)), Num(endpoint)));
        Formula rows = And(row(0, 1), row(22, 4), row(1, 0), row(23, 3));
        return Disp(Forall("N", Nat(), rows));
    }

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Neq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mod(Formula left, Formula right) =>
        new Formula.Modulo(left, right);
    private static Formula Pow(Formula left, Formula right) =>
        new Formula.Power(left, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(params Formula[] parts) => parts.Aggregate(
        (left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Forall(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Num(long value) => new Formula.Number(value);
}
