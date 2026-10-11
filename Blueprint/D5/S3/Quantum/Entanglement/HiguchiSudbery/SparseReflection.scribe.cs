using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.HiguchiSudbery;

internal sealed class SparseReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse monomials are lists of variable indices with integer coefficients. The fuelled sorting laws ref_mergeFuel_perm and ref_sortFuel_perm preserve permutations. The laws ref_eval_termMul and ref_eval_mul show that evaluation respects products. The variables ref_vars pair each amplitude with its conjugate; ref_eval_swap and ref_eval_swap_vars identify index swapping with complex conjugation. The norm polynomial ref_normPoly, cubic forms ref_q0 through ref_q271, and minor polynomials ref_m0 through ref_m47 give the exact certificate data.",
        H("SparseReflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ref-mergefuel"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/SparseReflection.ref_mergeFuel"),
                H("Merging with bounded fuel"),
                StatementSource.FromAuthor(Disp(MergeDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four equations are the defining clauses, in order. Type* permits any universe. The comparator returns Bool; the conditional tests that Boolean value. At zero fuel the lists are appended, and at successor fuel one head is selected whenever both lists are nonempty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ref-mergefuel-perm"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/SparseReflection.ref_mergeFuel_perm"),
                H("Merging preserves the input permutation"),
                StatementSource.FromAuthor(Disp(MergePermutation())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every comparator, fuel and pair of lists, ref_mergeFuel produces a List.Perm of their concatenation. No ordering or comparator laws are assumed. Induction on the fuel treats the two selected-head branches and the exhausted-fuel clause."))),
                DescribeRole.Theorem),
            Paragraph(Text("Sparse monomials are lists of variable indices with integer coefficients. The fuelled sorting laws ref_mergeFuel_perm and ref_sortFuel_perm preserve permutations. The laws ref_eval_termMul and ref_eval_mul show that evaluation respects products. The variables ref_vars pair each amplitude with its conjugate; ref_eval_swap and ref_eval_swap_vars identify index swapping with complex conjugation. The norm polynomial ref_normPoly, cubic forms ref_q0 through ref_q271, and minor polynomials ref_m0 through ref_m47 give the exact certificate data.")),
            Paragraph(Text("The prime encoding represents monomial keys by products of primes. The function prime_decodeTable reads blocks of sixteen base-2^60 words, with signed coefficients in their lowest 21 bits. This module holds the shared encoding definitions and the data and kernel checks for chunks 4 through 11, 18, and 48 through 55. PrimeReflection proves the prime evaluation laws, and PrimeHierarchyCertificate consumes the checked chunks in prime_eval_combined.")))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        All(F.Id(name), type, body);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(name, Sp, Colon, Sp, type)),
            Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula And(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));
    private static Formula ListOf(Formula type) => Call("List", type);
    private static Formula Append(Formula p, Formula q) => Seq(p, Plus, Plus, q);
    private static Formula Cons(Formula x, Formula xs) => Seq(x, Colon, Colon, xs);
    private static Formula Nil => Seq(OpenBracket, CloseBracket);
    private static Formula Merge(Formula le, Formula n, Formula p, Formula q) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("ref"), Underscore, Grp(F.Id("mergeFuel")))), [le, n, p, q]);
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Call("if"), Sp, Parenthesized(condition), Sp, Call("then"), Sp,
            Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no));
    private static Formula Comparator(Formula alpha) =>
        new Formula.TypeArrow(alpha, new Formula.TypeArrow(alpha, Call("Bool")));

    private static Formula MergeDefinition()
    {
        var alpha = Alpha;
        var le = F.Id("le");
        var n = F.Id("n");
        var p = F.Id("p");
        var q = F.Id("q");
        var x = F.Id("x");
        var y = F.Id("y");
        var xs = F.Id("xs");
        var ys = F.Id("ys");
        var next = Seq(n, Plus, D(1));
        var zero = All("p", ListOf(alpha), All("q", ListOf(alpha),
            Equal(Merge(le, D(0), p, q), Append(p, q))));
        var leftEmpty = All("n", Call("Nat"), All("q", ListOf(alpha),
            Equal(Merge(le, next, Nil, q), q)));
        var rightEmpty = All("n", Call("Nat"), All("p", ListOf(alpha),
            Equal(Merge(le, next, p, Nil), p)));
        var nonempty = All("n", Call("Nat"), All("x", alpha,
            All("xs", ListOf(alpha), All("y", alpha, All("ys", ListOf(alpha),
                Equal(Merge(le, next, Cons(x, xs), Cons(y, ys)),
                    IfThenElse(new Formula.Apply(le, [x, y]),
                        Cons(x, Merge(le, n, xs, Cons(y, ys))),
                        Cons(y, Merge(le, n, Cons(x, xs), ys)))))))));
        return All(alpha, Seq(Call("Type"), Star), All("le", Comparator(alpha),
            And(zero, And(leftEmpty, And(rightEmpty, nonempty)))));
    }

    private static Formula MergePermutation()
    {
        var alpha = Alpha;
        var le = F.Id("le");
        var n = F.Id("n");
        var p = F.Id("p");
        var q = F.Id("q");
        return All(alpha, Seq(Call("Type"), Star), All("le", Comparator(alpha),
            All("n", Call("Nat"), All("p", ListOf(alpha), All("q", ListOf(alpha),
                Qualified("List", "Perm", Merge(le, n, p, q), Append(p, q)))))));
    }
}
