using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate.BalancedSU2CommutatorNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class BalancedSU2CommutatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Approximate/BalancedSU2Commutator.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A determinant-one two-dimensional unitary is exactly a commutator of determinant-one unitaries at square-root distance from identity.",
        H("Balanced commutators in SU(2)"),Blocks(
            Paragraph(Text("Mat denotes complex 2 by 2 matrices with the Euclidean L2 operator norm. SU(U) means unitarity and determinant one. star is the matrix adjoint, so VW star(V) star(W) is the group commutator. All statements and proofs in this support module are Apache-2.0 reuse of Zayn Blore's CSD SU2Rotation and CommutatorDecomposition at commit 9b2d2c17e926ae13795119c5f2f62e85ea240c2d. Original file and declaration references are in the Lean source; the full license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.")),
            Describe.Lean(DescribeId.Create("quaternion-distance"),DeclarationHandle.Create(Prefix+"norm_su2_sub_one"),
                H("Distance of a unit quaternion matrix"),StatementSource.FromAuthor(QuaternionNorm()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/dawsonnielsen2006solovaykitaev")),
                Blocks(Paragraph(Text("The scalar part of a unit quaternion determines its operator-norm distance to identity. The C-star identity reduces this to star(M)M being a scalar multiple of the identity."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-su-commutator"),DeclarationHandle.Create(Prefix+"exists_commutator_of_det_one"),
                H("Exact balanced decomposition"),StatementSource.FromAuthor(Decomposition()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/dawsonnielsen2006solovaykitaev")),
                Blocks(Paragraph(Text("Write the target as a unit quaternion. Two rotations about orthogonal axes produce a standard commutator at exactly the target distance from identity; its scalar part therefore agrees with the target. Reflection through the bisector aligns their vector parts. In the antipodal case, swap the two factors to take the adjoint. Unitary conjugation preserves both factor distances and determinant one. The decomposition is exact, with both factors bounded by sqrt(2)*sqrt(norm(U-1))."))),DescribeRole.Theorem))));

    private static Formula QuaternionNorm()
    {
        Formula w=X("w"),x=X("x"),y=X("y"),z=X("z");
        Formula unit=Eq(Add(Add(Add(Pow(w,N(2)),Pow(x,N(2))),Pow(y,N(2))),Pow(z,N(2))),N(1));
        Formula result=Eq(Norm(Subtract(Call("suTwo",w,x,y,z),N(1))),Call("sqrt",Subtract(N(2),Multiply(N(2),w))));
        return All("w",Call("Real"),All("x",Call("Real"),All("y",Call("Real"),All("z",Call("Real"),Imp(unit,result)))));
    }
    private static Formula Decomposition()
    {
        Formula u=X("U"),v=X("V"),w=X("W");
        Formula radius=Multiply(Call("sqrt",N(2)),Call("sqrt",Norm(Subtract(u,N(1)))));
        Formula result=Ex("V",Call("Mat"),Ex("W",Call("Mat"),And(Su(v),And(Su(w),
            And(Eq(u,Comm(v,w)),And(Le(Norm(Subtract(v,N(1))),radius),Le(Norm(Subtract(w,N(1))),radius)))))));
        return All("U",Call("Mat"),Imp(Su(u),result));
    }
}

internal static class BalancedSU2CommutatorNotation
{
    internal static Formula X(string n) => F.Id(n);
    internal static Formula N(long n) => new Formula.Number(n);
    internal static Formula All(string n, Formula t, Formula b) => new Formula.Bind(
        FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    internal static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(
        FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    internal static Formula At(Formula f, Formula x) => new Formula.Apply(f,[x]);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    internal static Formula Pos(Formula a) => Lt(N(0),a);
    internal static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    internal static Formula Norm(Formula a) => new Formula.Norm(a);
    internal static Formula Star(Formula a) => Call("star",a);
    internal static Formula Words(Formula m) => Call("List",Call("Fin",m));
    internal static Formula Su(Formula a) => And(Unitary(a),Eq(Call("det",a),N(1)));
    internal static Formula Unitary(Formula a) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,Call("unitary",Call("Mat")));
    internal static Formula Member(Formula a, Formula f) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,f);
    internal static Formula Eval(Formula g, Formula w) => Call("evalGamma",g,w);
    internal static Formula Inv(Formula s, Formula w) => Call("inverseWord",s,w);
    internal static Formula Error(Formula g, Formula u, Formula w) => Norm(Subtract(u,Eval(g,w)));
    internal static Formula Comm(Formula v, Formula w) => Multiply(Multiply(Multiply(v,w),Star(v)),Star(w));
    internal static Formula Exponent() => Frac(Call("log",N(5)),Call("log",Frac(N(3),N(2))));
    internal static Formula Alphabet(Formula body) => All("m",Call("Nat"),All("Gamma",
        new Formula.TypeArrow(Call("Fin",X("m")),Call("Mat")),body));
    internal static Formula Generators(Formula m, Formula g) => All("i",Call("Fin",m),Su(At(g,X("i"))));
    internal static Formula ChosenInverse(Formula m, Formula g, Formula s) => All("i",Call("Fin",m),
        Eq(At(g,At(s,X("i"))),Star(At(g,X("i")))));
    internal static Formula Density(Formula m, Formula g) => All("A",Call("Mat"),Imp(Su(X("A")),
        All("eta",Call("Real"),Imp(Pos(X("eta")),Ex("v",Words(m),Lt(Error(g,X("A"),X("v")),X("eta")))))));
    internal static Formula EventStatement()
    {
        Formula m=X("m"),g=X("Gamma"),k=X("K"),b=X("b"),e=X("epsilon"),u=X("U"),w=X("w");
        Formula inverse=All("i",Call("Fin",m),Ex("j",Call("Fin",m),
            Eq(At(g,X("j")),Star(At(g,X("i"))))));
        Formula paired=Ex("w",Words(m),And(Le(Error(g,u,w),e),
            Le(Call("real",Call("length",w)),Multiply(k,Pow(Call("log",Frac(N(1),e)),Exponent())))));
        Formula result=Ex("K",Call("Real"),Ex("b",Call("Real"),And(Pos(k),And(Pos(b),And(Lt(b,N(1)),
            All("epsilon",Call("Real"),Imp(And(Pos(e),Le(e,b)),All("U",Call("Mat"),Imp(Su(u),paired)))))))));
        return Alphabet(Imp(And(Generators(m,g),And(inverse,Density(m,g))),result));
    }
}
