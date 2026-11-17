using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeSaturationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeSaturation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coordinate routing realizes the complete rectangular width-three native saturation family.",
        H("Native saturation at the three-halves threshold"),
        Blocks(
            Paragraph(Text(
                "All dimensions are natural numbers. For every positive q, a width-three sum of " +
                "complex a-by-b and (3q)-by-(2q) tensor factors has identity column Gram exactly " +
                "when 2b is at most 3a. The family includes a=0 or b=0.")),
            Describe.Lean(
                DescribeId.Create("native-saturation-iff"),
                DeclarationHandle.Create(Owner + ".native_saturation_iff"),
                H("Rectangular native saturation iff"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural a and b and every positive natural q, there exist " +
                        "three complex matrices M(r) of size a by b and three matrices N(r) of " +
                        "size 3q by 2q whose tensor sum has FᴴF equal to the identity on " +
                        "Fin b × Fin (2q), if and only if 2b ≤ 3a. No premise a<b is present or " +
                        "needed, and zero dimensions remain part of the statement.")),
                    Paragraph(Text(
                        "Use zero-based coordinates and write [P] for 1 when P holds and 0 otherwise. " +
                        "The explicit left slices are M(0)(i,j)=[i=j], " +
                        "M(1)(i,j)=[a≤j and i=2(j-a)], and M(2)(i,j)=[a≤j and i=2(j-a)+1]. " +
                        "The right slices are N(0)(l,k)=[l=k], " +
                        "N(1)(l,k)=[k<q and l=2q+k], and N(2)(l,k)=[q≤k and l=q+k]. " +
                        "The differences j-a are natural subtraction and are used under a≤j.")),
                    Paragraph(Text(
                        "When 2b≤3a, these slices route each input (j,k) to (j,k) if j<a, " +
                        "to (2(j-a),2q+k) if a≤j and k<q, and to (2(j-a)+1,q+k) otherwise. " +
                        "The threshold puts both residual first coordinates below a. The first " +
                        "branch has second coordinate below 2q and the other branches have it " +
                        "at least 2q. The two residual branches have even and odd first " +
                        "coordinates. Within each branch the output recovers j and k, proving " +
                        "injectivity. Entrywise expansion identifies the tensor sum with its " +
                        "coordinate matrix, so SequentialRegisterCircuit.coordinate_gram gives " +
                        "the identity column Gram.")),
                    Paragraph(Text(
                        "For necessity, an identity column Gram has full column rank. The native " +
                        "matrix has 3aq rows and 2bq columns. Thus 2bq=rank(FᴴF)≤rank(F)≤3aq, " +
                        "and positivity of q gives 2b≤3a. If b=0 the column space is empty and " +
                        "the Gram equation is vacuous; if a=0, the threshold forces b=0.")),
                    Paragraph(Text(
                        "This whole-parameter construction is a consequence of the native model " +
                        "with fixed right dimensions c=2q and d=3q. The separate universal " +
                        "upper-bound question asks whether arbitrary c,d and a<b force 3c≤2d " +
                        "under the scalar-Gram hypotheses; that question remains unresolved.")),
                    Paragraph(Text(
                        "At a=2, b=3 and q=1 this recovers the existing permutation-coordinate " +
                        "example: (0,0),(0,1),(1,0),(1,1),(2,0),(2,1) route to " +
                        "(0,0),(0,1),(1,0),(1,1),(0,2),(1,2), respectively. This bijection " +
                        "gives the same six-coordinate permutation and is a reused instance.")),
                    Paragraph(Text(
                        "A literature search found arXiv:1612.07616v1, whose introduction, " +
                        "Theorem 1.3, Definition 3.1 and Lemma 3.2 concern square local factors; " +
                        "they do not state this rectangular iff. This document makes no external " +
                        "novelty claim."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumTerm(Formula index, Formula term) =>
        Seq(new Formula.Subscript(F.Sum, Seq(index, Colon, Call("Fin", D(3)))), Sp, term);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula rows, Formula cols) =>
        Call("Matrix", rows, cols, V("Complex"));
    private static Formula Factors(Formula rows, Formula cols) =>
        new Formula.TypeArrow(Fin(D(3)), Matrix(rows, cols));
    private static Formula Product(Formula left, Formula right) =>
        Call("Prod", left, right);

    private static Formula Statement()
    {
        Formula a = V("a"), b = V("b"), q = V("q");
        Formula r = V("r"), M = V("M"), N = V("N");
        Formula sum = SumTerm(r, Call("kronecker", Apply(M, r), Apply(N, r)));
        Formula gram = Equal(
            Mul(Call("conjTranspose", sum), sum),
            Typed(D(1), Matrix(Product(Fin(b), Fin(Mul(D(2), q))),
                Product(Fin(b), Fin(Mul(D(2), q))))));
        Formula witness = Some("M", Factors(Fin(a), Fin(b)),
            Some("N", Factors(Fin(Mul(D(3), q)), Fin(Mul(D(2), q))), gram));
        Formula body = All("hq", Lt(D(0), q),
            new Formula.Logic(Parenthesized(witness), FormulaLogicOperator.Iff,
                Parenthesized(Le(Mul(D(2), b), Mul(D(3), a)))));
        return All("a", V("Nat"), All("b", V("Nat"), All("q", V("Nat"), body)));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(Open, value, Colon, Sp, type, Close);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
