using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.ErdosNicolas;

internal sealed class ErdosNicolasDivisorBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/ErdosNicolas/DivisorBlocks.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/erdosnicolas1989functions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power divisor blocks", H("Prime-power divisor blocks"), Blocks(
            Describe.Lean(DescribeId.Create("erdosnicolas-divisorblocks-partition"),
                DeclarationHandle.Create(Prefix + "prime_power_divisors_partition"),
                H("A two-block covering of the divisor set"),
                StatementSource.FromAuthor(Disp(PartitionFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a prime p and a positive exponent a, every divisor of p^a m either divides m or is p times a divisor of p^(a-1) m. If p divides the divisor, cancel one copy of p; otherwise coprimality removes the prime power. The equality includes m=0, when both sides are empty. The blocks can overlap for general m. Under the additional hypothesis that p does not divide m, they are disjoint, their cardinalities are tau(m) and a tau(m), and their union has cardinality (a+1) tau(m). These are the two sets used by the prime-power kernel criterion."))),
                DescribeRole.Theorem))));

    private static Formula PartitionFormula()
    {
        var p = V("p"); var a = V("a"); var m = V("m");
        var previous = Mul(Pow(p, Sub(a, D(1))), m);
        var scaled = Call("image", Call("mulBy", p), Call("divisors", previous));
        Formula body = Eq(Call("divisors", Mul(Pow(p, a), m)),
            Call("union", Call("divisors", m), scaled));
        body = Imp(Lt(D(0), a), body);
        body = Imp(Call("Prime", p), body);
        return All("p", Nat(), All("a", Nat(), All("m", Nat(), body)));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
