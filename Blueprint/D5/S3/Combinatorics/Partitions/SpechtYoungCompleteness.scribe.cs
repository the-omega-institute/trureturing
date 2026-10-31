using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtYoungCompletenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completeness of the ordinary Specht traces", H("Completeness of the ordinary Specht traces"), Blocks(
            Paragraph(Text("For every natural degree n, SComplex(mu) is the existing complex scalar extension of the rational polytabloid representation of the literal diagram YoungDiagram.ofPartition mu. MComplex(nu) is the existing complex permutation representation on cosets of youngSubgroup nu. trace(mu,pi) is the trace of the actual action of pi on SComplex(mu). psi(nu,pi) is the character of MComplex(nu). Multiplicity(mu,nu) is the complex dimension of the category Hom from SComplex(mu) to MComplex(nu), read in Complex when it multiplies a trace. Pairing is the existing D5 bilinear character pairing, normalized by the inverse of the order of the permutation group and using the inverse in its second argument. Orthogonality gives linear independence of the actual traces. Class functions are linearly equivalent to functions on conjugacy classes, and the literal partition to conjugacy class equivalence gives the matching dimension. The traces therefore form a basis. Pairing with a Young permutation character computes its coordinates as the actual Hom dimensions. Expanding one permutation character and pairing with the other gives their Gram identity. The argument includes n equal to zero and imposes no alphabet bound.")),
            Describe.Lean(DescribeId.Create("eq-sum-spechttrace"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungCompleteness.eq_sum_spechtTrace"),
                H("Every class function expands in actual Specht traces"), StatementSource.FromAuthor(Expansion()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("char-permutationmodulecomplex-eq-sum-multiplicity-mul-spechttrace"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungCompleteness.char_permutationModuleℂ_eq_sum_multiplicity_mul_spechtTrace"),
                H("The actual Young permutation character decomposition"), StatementSource.FromAuthor(YoungExpansion()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-char-permutationmodulecomplex-mul-char-permutationmodulecomplex"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungCompleteness.sum_char_permutationModuleℂ_mul_char_permutationModuleℂ"),
                H("The actual multiplicity Gram matrix"), StatementSource.FromAuthor(Gram()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Open, b, Close);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, type)), Sp, Open, body, Close);
    private static Formula Nat() => Call("Nat");
    private static Formula Complex() => Call("Complex");
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula Perm(Formula n) => Call("Perm", Call("Fin", n));

    private static Formula Trace(Formula mu, Formula pi) => Call("trace", mu, pi);
    private static Formula Psi(Formula nu, Formula pi) => Call("psi", nu, pi);
    private static Formula M(Formula mu, Formula nu) => Call("complexNatCast", Call("Multiplicity", mu, nu));
    private static Formula Expansion()
    {
        Formula n = Id("n"), f = Id("f"), mu = Id("mu"), pi = Id("pi");
        return Disp(All("n", Nat(), All("f", Call("ClassFunction", Complex(), Perm(n)),
            All("pi", Perm(n), Eq(Call("apply", f, pi), SumOver("mu", Part(n), Mul(
                Call("Pairing", Call("ofCharacter", Call("SComplex", mu)), f), Trace(mu, pi))))))));
    }
    private static Formula YoungExpansion()
    {
        Formula n = Id("n"), nu = Id("nu"), mu = Id("mu"), pi = Id("pi");
        return Disp(All("n", Nat(), All("nu", Part(n), All("pi", Perm(n), Eq(Psi(nu, pi),
            SumOver("mu", Part(n), Mul(M(mu, nu), Trace(mu, pi))))))));
    }
    private static Formula Gram()
    {
        Formula n = Id("n"), nu = Id("nu"), xi = Id("xi"), mu = Id("mu"), pi = Id("pi");
        return Disp(All("n", Nat(), All("nu", Part(n), All("xi", Part(n), Eq(
            SumOver("pi", Perm(n), Mul(Psi(nu, pi), Psi(xi, pi))),
            Mul(Call("complexNatCast", Call("factorial", n)),
                SumOver("mu", Part(n), Mul(M(mu, nu), M(mu, xi)))))))));
    }

}
