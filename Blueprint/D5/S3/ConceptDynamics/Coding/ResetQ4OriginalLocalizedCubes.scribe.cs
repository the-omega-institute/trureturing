using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class ResetQ4OriginalLocalizedCubesDocument : IScribeDocumentDefinition
{
    private static Formula I(string s) => FormulaDsl.Id(s);
    private static Formula.BoundVariable B(string s, Formula t) => new(FormulaIdentifier.Create(s), t);
    private static Formula All(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [..v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [..v], f);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Power(Formula x, Formula n) => Call("pow", x, n);
    private static Formula Value(string x) => Call("matrixValue", I(x));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic Bezout gluing transports original quartic unit cube forms to every original history automorphism.",
        H("Dyadic cube factorization of the original reset action"), Blocks(
            Paragraph(Text("Let D=Int[1/2] and index matrices by the eight original signed vertices "
                + "Sigma (_:Fin 4), Sign. The actual full group is ResetFullAut(4). "
                + "Transport its original beam-set-image action rho through resetNativeEquiv to "
                + "the original vertex module, take its column matrix, and extend coefficients "
                + "from Int to D; this defines rhoD. T is the column matrix of the literal "
                + "forward reset transition, with the same scalar extension. It is the transpose "
                + "of the expanded row adjacency. The original unit shift has image T, and the "
                + "original evenAut(4) has image I+T.")),
            Paragraph(Text("Write f=X^4-X^3-X^2-X-1, g=X^4+X^3+X^2+X+1, and F=f*g. "
                + "The integral certificate X*f+(2-X)*g=2 gives "
                + "(X/2)*f+(1-X/2)*g=1 over D. Thus the original quotient D[X]/(F) "
                + "is isomorphic to D[X]/(f) times D[X]/(g). The two projectors are "
                + "(1-X/2)*g and (X/2)*f. Monic representatives give the inverse map. "
                + "Component units and their inverses glue together without any residue "
                + "compatibility requirement on the chosen roots.")),
            Paragraph(Text("For each actual h, the published scalarUnit construction gives an "
                + "integral unit u_h in Int[X]/(F), from the action rho(h) and its inverse. "
                + "Its components are compatible modulo two. ResetQ4UnitCubes supplies "
                + "u_plus=alpha^i*Bplus^j*v^3 and u_minus=Bminus^k*w^3 with i,j,k in Fin 3. "
                + "Compatibility forces j=k. Time has components (alpha,beta), while I+time "
                + "has components (Bplus,Bminus). Since beta^5=1, replacing w by beta^(3*i)*w "
                + "gives beta^i*(beta^(3*i)*w)^3=w^3. This exact correction aligns the "
                + "two component forms before the roots are glued.")),
            Paragraph(Text("The cyclic integral chart and the original vertex basis identify "
                + "multiplication by X with forward T. Polynomial ring-hom extensionality "
                + "then gives F(T)=0 and the evaluation identity for every integral scalar, "
                + "including u_h. Evaluation descends from D[X]/(F) to the original matrix "
                + "ring. Evaluating a glued unit also evaluates its actual inverse, and "
                + "commutativity of the source proves that its matrix commutes with T. "
                + "Centralizer is the subgroup of matrix units centralizing the unit with "
                + "matrix value T.")),
            Describe.Lean(DescribeId.Create("original-localized-cube-factorization"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.original_localized_cube_factorization"),
                H("Every original automorphism has a commuting dyadic cube factorization"),
                StatementSource.FromAuthor(Disp(All(Ex(And(
                    Equal(Call("rhoD", I("h")), Multiply(Multiply(
                        Power(I("T"), Call("val", I("i"))),
                        Power(Add(Num(1), I("T")), Call("val", I("j")))),
                        Power(Value("v"), Num(3)))),
                    Call("Commute", Value("v"), I("T"))),
                    B("i", Call("Fin", Num(3))), B("j", Call("Fin", Num(3))),
                    B("v", I("Centralizer"))), B("h", Call("ResetFullAut", Num(4)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The matrix V is a genuine unit over D and commutes with the literal forward T. "
                    + "The proof factors the actual integral scalar unit, then evaluates the factorization "
                    + "in the original action diagram. The bounded exponents are representatives modulo "
                    + "three; no uniqueness of them or of the cube root is asserted."))), DescribeRole.Theorem),
            Paragraph(Text("The conclusion constrains every actual original image but does not assert "
                + "that every centralizing matrix is an image. It supplies neither a presentation of "
                + "the full original group nor an SGCC character or cochain. Given a separately supplied "
                + "additive character of the full matrix-unit centralizer with values in ZMod(3) "
                + "that kills the original shift, a cube contributes zero and each original image "
                + "has character value j times the value at I+T. This conditional application "
                + "constructs no character and proves no nonzero value at I+T.")) )));
}
