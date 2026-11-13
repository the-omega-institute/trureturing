using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate.SolovayKitaevNotation;

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
                AssessedProvenance.FromLiterature("dawsonnielsen2006solovaykitaev"),
                Blocks(Paragraph(Text("The scalar part of a unit quaternion determines its operator-norm distance to identity. The C-star identity reduces this to star(M)M being a scalar multiple of the identity."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-su-commutator"),DeclarationHandle.Create(Prefix+"exists_commutator_of_det_one"),
                H("Exact balanced decomposition"),StatementSource.FromAuthor(Decomposition()),
                AssessedProvenance.FromLiterature("dawsonnielsen2006solovaykitaev"),
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
